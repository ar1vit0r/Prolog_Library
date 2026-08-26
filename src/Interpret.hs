-- | Prolog interpreter: depth-first clause resolution with backtracking,
-- built-in predicates, cuts, negation as failure, and fresh variable generation.
module Interpret
       ( queryResult
       , interpret
       , resolve
       ) where

import Control.Monad (guard)
import System.IO.Unsafe (unsafePerformIO)
import Term
import Unify (unify, substituteAll, mergeSubst)
import FreshVars (freshenClauseIO, renameIO)

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
interpret _ (Func "=" [x, y]) (subst, cut) =
  case unify x y of
    Nothing -> []
    Just sub -> [(mergeSubst subst sub, cut)]
interpret _ (Func "is" [x, expr]) (subst, cut) =
  case eval subst expr of
    Just val -> case unify (substituteAll subst x) (Atom (show val)) of
      Just sub -> [(mergeSubst subst sub, cut)]
      Nothing -> []
    Nothing -> []
interpret _ (Func "=\\=" [a, b]) (subst, cut) = evalCmp (/=) subst a b cut
interpret _ (Func "=:=" [a, b]) (subst, cut) = evalCmp (==) subst a b cut
interpret _ (Func "<" [a, b]) (subst, cut) = evalCmp (<) subst a b cut
interpret _ (Func ">" [a, b]) (subst, cut) = evalCmp (>) subst a b cut
interpret _ (Func "=<" [a, b]) (subst, cut) = evalCmp (<=) subst a b cut
interpret _ (Func ">=" [a, b]) (subst, cut) = evalCmp (>=) subst a b cut
interpret prog (Func "findall" [template, goal, resultList]) (subst, cut) =
  let solutions = interpret prog goal ([], False)
      values = [resolve soln template | (soln, _) <- solutions]
      listTerm = foldr (\v acc -> Func "." [v, acc]) (Atom "[]") values
  in case unify listTerm resultList of
       Nothing -> []
       Just sub' -> [(mergeSubst subst sub', cut)]
interpret prog (Func "bagof" [template, goal, resultList]) (subst, cut) =
  let solutions = interpret prog goal ([], False)
  in if null solutions then [] else
       let values = [resolve soln template | (soln, _) <- solutions]
           listTerm = foldr (\v acc -> Func "." [v, acc]) (Atom "[]") values
       in case unify listTerm resultList of
            Nothing -> []
            Just sub' -> [(mergeSubst subst sub', cut)]
interpret prog term (_, _) = concatMap tryClause matchingClauses
  where
    matchingClauses = filter (matches term . headOf) prog

    headOf (t :- _)   = t
    headOf (Simple t) = t

    matches Cut Cut               = True
    matches (Atom x) (Atom y)     = x == y
    matches (Var _) _             = True
    matches _ (Var _)             = True
    matches (Func n1 a1) (Func n2 a2) =
      n1 == n2 && length a1 == length a2 && all (uncurry matches) (zip a1 a2)
    matches (Not t1) (Not t2)     = matches t1 t2
    matches _ _                   = False

    tryClause c =
      -- unsafePerformIO: safe here because the interpreter is single-threaded
      let freshened = unsafePerformIO (freshenClauseIO c)
      in case unify (headOf freshened) term of
           Nothing -> []
           Just sub -> case freshened of
             Simple _ -> [(sub, False)]
             _ :- body ->
               let bodyGoals = map (substituteAll sub) body
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
