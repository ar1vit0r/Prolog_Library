-- | Prolog interpreter: depth-first clause resolution with backtracking,
-- built-in predicates, cuts, negation as failure, and fresh variable generation.
-- Relies on the project's -fno-cse -fno-full-laziness ghc-options (see the
-- .cabal file): without them, GHC can share/cache unsafePerformIO reads of
-- dynamicDB across syntactically identical interpret calls.
module Interpret
       ( queryResult
       , interpret
       , resolve
       ) where

import Control.Monad (guard)
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import Term
import Unify (unify, substituteAll, mergeSubst)
import FreshVars (renameIO, renameIOAcc, renameManyIOAcc)

-- | Clauses added at runtime via assert/asserta/retract. A single global
-- store (not scoped per Prolog program) is fine for this single-threaded,
-- single-session interpreter; see assert/retract built-ins below.
{-# NOINLINE dynamicDB #-}
dynamicDB :: IORef Prolog
dynamicDB = unsafePerformIO (newIORef [])

-- | Remove the first dynamic fact whose head unifies with the target term.
-- Returns whether a clause was found and removed.
retractFirst :: Term -> IO Bool
retractFirst target = do
  db <- readIORef dynamicDB
  case break isMatch db of
    (_, [])          -> return False
    (before, _:after) -> writeIORef dynamicDB (before ++ after) >> return True
  where
    isMatch (Simple h) = case unify h target of
      Just _  -> True
      Nothing -> False
    isMatch (_ :- _)   = False

-- | Apply an update to the dynamic clause store and succeed unconditionally.
doAssert :: (Prolog -> Prolog) -> Subst -> Bool -> [CutState]
doAssert update subst cut =
  unsafePerformIO (modifyIORef dynamicDB update) `seq` [(subst, cut)]


-- | The head term of a clause.
headOf :: Clause -> Term
headOf (t :- _)   = t
headOf (Simple t) = t

-- | A predicate's name/arity signature, for built-in-vs-user-clause checks.
predSig :: Term -> Maybe (String, Int)
predSig (Func n args) = Just (n, length args)
predSig (Atom n)      = Just (n, 0)
predSig _             = Nothing

-- | True if the program defines its own clause(s) for this term's
-- predicate, in which case a built-in of the same name/arity must not
-- shadow them.
isUserDefined :: Prolog -> Term -> Bool
isUserDefined prog t = case predSig t of
  Nothing  -> False
  Just sig -> any (\c -> predSig (headOf c) == Just sig) prog

-- | Run a query against a Prolog program, returning the first solution as
-- [(varname, prettyprinted value)]. Unbound variables are skipped.
queryResult :: Prolog -> Term -> [(String, String)]
queryResult prog term =
  -- unsafePerformIO: safe here because the interpreter is single-threaded
  -- and renameIO only reads/writes the global counter.
  let (renamedTerm, mapping) = unsafePerformIO (renameIO term)
      solutions = interpret prog renamedTerm ([], False)
  in case solutions of
       [] -> []
       (subst, _) : _ ->
         [(orig, val) | (orig, rn) <- mapping
         , let resolved = resolve subst (Var rn)
         , case resolved of
             Var _ -> False  -- skip unbound variables
             _ -> True
         , let val = prettyTerm resolved
         , not (null val)]

-- | Fully resolve a term through a substitution chain until it stabilizes.
resolve :: Subst -> Term -> Term
resolve s t
  | t' == t    = t
  | otherwise  = resolve s t'
  where t' = substituteAll s t

-- | Interpret a Prolog goal against a clause database, returning all solutions.
-- Built-in predicates (=, is, comparisons, findall, bagof) are handled inline.
-- Cut fires immediately and prevents further backtracking.
interpret :: Prolog -> Term -> CutState -> [CutState]
interpret _ _ (subst, True) = [(subst, True)]
interpret prog t@(Func "=" [x, y]) (subst, cut)
  | not (isUserDefined prog t) =
      case unify x y of
        Nothing -> []
        Just sub -> [(mergeSubst subst sub, cut)]
interpret prog t@(Func "is" [x, expr]) (subst, cut)
  | not (isUserDefined prog t) =
      case eval subst expr of
        Just val -> case unify (substituteAll subst x) (Atom (show val)) of
          Just sub -> [(mergeSubst subst sub, cut)]
          Nothing -> []
        Nothing -> []
interpret prog t@(Func "=\\=" [a, b]) (subst, cut)
  | not (isUserDefined prog t) = evalCmp (/=) subst a b cut
interpret prog t@(Func "=:=" [a, b]) (subst, cut)
  | not (isUserDefined prog t) = evalCmp (==) subst a b cut
interpret prog t@(Func "<" [a, b]) (subst, cut)
  | not (isUserDefined prog t) = evalCmp (<) subst a b cut
interpret prog t@(Func ">" [a, b]) (subst, cut)
  | not (isUserDefined prog t) = evalCmp (>) subst a b cut
interpret prog t@(Func "=<" [a, b]) (subst, cut)
  | not (isUserDefined prog t) = evalCmp (<=) subst a b cut
interpret prog t@(Func ">=" [a, b]) (subst, cut)
  | not (isUserDefined prog t) = evalCmp (>=) subst a b cut
interpret prog t@(Func "findall" [template, goal, resultList]) (subst, cut)
  | not (isUserDefined prog t) =
      let solutions = interpret prog goal ([], False)
          values = [resolve soln template | (soln, _) <- solutions]
      in case unify (list values) resultList of
           Nothing -> []
           Just sub' -> [(mergeSubst subst sub', cut)]
interpret prog t@(Func "bagof" [template, goal, resultList]) (subst, cut)
  | not (isUserDefined prog t) =
      let solutions = interpret prog goal ([], False)
      in if null solutions then [] else
           let values = [resolve soln template | (soln, _) <- solutions]
           in case unify (list values) resultList of
                Nothing -> []
                Just sub' -> [(mergeSubst subst sub', cut)]
interpret prog (Not g) (subst, cut) =
  if null (interpret prog g ([], False))
  then [(subst, cut)]
  else []
-- assert/assertz/asserta/retract only handle facts (Simple clauses): the
-- parser has no infix ':-' operator at Term level, so an asserted rule
-- body can't be written as a builtin argument yet.
interpret prog t@(Func "assert" [factTerm]) (subst, cut)
  | not (isUserDefined prog t) = doAssert (++ [Simple (substituteAll subst factTerm)]) subst cut
interpret prog t@(Func "assertz" [factTerm]) (subst, cut)
  | not (isUserDefined prog t) = doAssert (++ [Simple (substituteAll subst factTerm)]) subst cut
interpret prog t@(Func "asserta" [factTerm]) (subst, cut)
  | not (isUserDefined prog t) = doAssert (Simple (substituteAll subst factTerm) :) subst cut
interpret prog t@(Func "retract" [factTerm]) (subst, cut)
  | not (isUserDefined prog t) =
      if unsafePerformIO (retractFirst (substituteAll subst factTerm))
      then [(subst, cut)]
      else []
interpret prog term (_, _) = concatMap tryClause matchingClauses
  where
    matchingClauses = filter (matches term . headOf) (prog ++ unsafePerformIO (readIORef dynamicDB))

    matches Cut Cut               = True
    matches (Atom x) (Atom y)     = x == y
    matches (Var _) _             = True
    matches _ (Var _)             = True
    matches (Func n1 a1) (Func n2 a2) =
      n1 == n2 && length a1 == length a2 && all (uncurry matches) (zip a1 a2)
    matches (Not t1) (Not t2)     = matches t1 t2
    matches _ _                   = False

    -- unsafePerformIO: safe here because the interpreter is single-threaded.
    -- The head is renamed and unified first; the (potentially larger) body
    -- is only renamed if the head actually unifies, so clauses that don't
    -- match skip the extra IO and traversal.
    tryClause c =
      let (freshHead, acc) = unsafePerformIO (renameIOAcc (headOf c) [])
      in case unify freshHead term of
           Nothing -> []
           Just sub -> case c of
             Simple _ -> [(sub, False)]
             _ :- body ->
               let freshBody = unsafePerformIO (fst <$> renameManyIOAcc acc body)
                   bodyGoals = map (substituteAll sub) freshBody
                   bodyResults = interpretBody prog bodyGoals ([], False)
               in [(mergeSubst sub bodySub, bodyCut) | (bodySub, bodyCut) <- bodyResults]

    interpretBody _ [] cs = [cs]
    interpretBody p (Cut:gs) (accSub, _) = interpretBody p gs (accSub, True)
    interpretBody p (Not g:gs) (accSub, accCut) =
      let solutions = interpret p g ([], False)
      in if null solutions
         then interpretBody p gs (accSub, accCut)
         else []
    interpretBody p (g:gs) (accSub, accCut) =
      concatMap tryGoal (interpret p g ([], False))
      where
        tryGoal (sub, subCut) =
          let newSub = mergeSubst accSub sub
              newCut = accCut || subCut
              gs' = map (substituteAll sub) gs
          in if subCut
             then interpretBody p gs' (newSub, True)
             else interpretBody p gs' (newSub, newCut)

-- | Evaluate an arithmetic expression to an Int. Only handles Ints parsed
-- from atom text; variables are looked up in the substitution.
eval :: Subst -> Term -> Maybe Int
eval _ (Atom s) = case reads s :: [(Int, String)] of
  [(n, "")] -> Just n
  _         -> Nothing
eval subst (Var x) = lookup x subst >>= eval subst
eval subst (Func "+" [a, b]) = (+) <$> eval subst a <*> eval subst b
eval subst (Func "-" [a, b]) = (-) <$> eval subst a <*> eval subst b
eval subst (Func "*" [a, b]) = (*) <$> eval subst a <*> eval subst b
eval subst (Func "/" [a, b]) = do
  x <- eval subst a
  y <- eval subst b
  guard (y /= 0)
  return (x `div` y)
eval subst (Func "mod" [a, b]) = do
  x <- eval subst a
  y <- eval subst b
  guard (y /= 0)
  return (x `mod` y)
eval _ _ = Nothing

-- | Evaluate a comparison between two terms. Returns the cut state if the
-- comparison holds, empty list otherwise.
evalCmp :: (Int -> Int -> Bool) -> Subst -> Term -> Term -> Bool -> [CutState]
evalCmp cmp subst a b cut =
  case (eval subst a, eval subst b) of
    (Just x, Just y) | x `cmp` y -> [(subst, cut)]
    _ -> []
