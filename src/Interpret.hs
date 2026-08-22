module Interpret
       ( queryResult
       , interpret
       ) where

import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad (guard, foldM)
import Term
import Unify (unify, substituteAll, mergeSubst)

{-# NOINLINE counter #-}
counter :: IORef Int
counter = unsafePerformIO (newIORef 0)

freshVarIO :: IO String
freshVarIO = do
  n <- readIORef counter
  writeIORef counter (n + 1)
  return ("_V" ++ show n)

collectVars :: Term -> [String]
collectVars (Atom _) = []
collectVars Cut = []
collectVars (Var x) = [x]
collectVars (Func _ args) = concatMap collectVars args
collectVars (Not t) = collectVars t

collectClauseVars :: Clause -> [String]
collectClauseVars (Simple t) = collectVars t
collectClauseVars (t :- body) = collectVars t ++ concatMap collectVars body

unique :: Eq a => [a] -> [a]
unique [] = []
unique (x:xs) = x : unique (filter (/= x) xs)

freshenClauseIO :: Clause -> IO Clause
freshenClauseIO c = do
  let allVars = unique (collectClauseVars c)
  mapping <- mapM (\v -> do { v' <- freshVarIO; return (v, v') }) allVars
  return (applyClauseMapping mapping c)

applyClauseMapping :: [(String, String)] -> Clause -> Clause
applyClauseMapping m (Simple t) = Simple (applyTermMapping m t)
applyClauseMapping m (t :- body) =
  applyTermMapping m t :- map (applyTermMapping m) body

applyTermMapping :: [(String, String)] -> Term -> Term
applyTermMapping _ (Atom x) = Atom x
applyTermMapping _ Cut = Cut
applyTermMapping m (Var x) = case lookup x m of
  Just x' -> Var x'
  Nothing -> Var x
applyTermMapping m (Func n args) = Func n (map (applyTermMapping m) args)
applyTermMapping m (Not t) = Not (applyTermMapping m t)

renameIO :: Term -> IO (Term, [(String, String)])
renameIO t = do
  (t', mapping) <- renameIOAcc t []
  return (t', mapping)

renameIOAcc :: Term -> [(String, String)] -> IO (Term, [(String, String)])
renameIOAcc (Atom x) acc = return (Atom x, acc)
renameIOAcc Cut acc = return (Cut, acc)
renameIOAcc (Var x) acc = case lookup x acc of
  Just freshName -> return (Var freshName, acc)
  Nothing -> do
    freshName <- freshVarIO
    return (Var freshName, acc ++ [(x, freshName)])
renameIOAcc (Func n args) acc = do
  (args', acc') <- foldM go ([], acc) args
  return (Func n (reverse args'), acc')
  where
    go (as, a) arg = do
      (arg', a') <- renameIOAcc arg a
      return (arg':as, a')
renameIOAcc (Not t) acc = do
  (t', acc') <- renameIOAcc t acc
  return (Not t', acc')

queryResult :: Prolog -> Term -> [(String, String)]
queryResult prog term =
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
  where
    resolve s t
      | t' == t    = t
      | otherwise  = resolve s t'
      where t' = substituteAll s t

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
interpret _ (Func "=\\=" [a, b]) (subst, cut) =
  case (eval subst a, eval subst b) of
    (Just x, Just y) | x /= y -> [(subst, cut)]
    _ -> []
interpret _ (Func "=:=" [a, b]) (subst, cut) =
  case (eval subst a, eval subst b) of
    (Just x, Just y) | x == y -> [(subst, cut)]
    _ -> []
interpret _ (Func "<" [a, b]) (subst, cut) =
  case (eval subst a, eval subst b) of
    (Just x, Just y) | x < y -> [(subst, cut)]
    _ -> []
interpret _ (Func ">" [a, b]) (subst, cut) =
  case (eval subst a, eval subst b) of
    (Just x, Just y) | x > y -> [(subst, cut)]
    _ -> []
interpret _ (Func "=<" [a, b]) (subst, cut) =
  case (eval subst a, eval subst b) of
    (Just x, Just y) | x <= y -> [(subst, cut)]
    _ -> []
interpret _ (Func ">=" [a, b]) (subst, cut) =
  case (eval subst a, eval subst b) of
    (Just x, Just y) | x >= y -> [(subst, cut)]
    _ -> []
interpret prog (Func "findall" [template, goal, resultList]) (subst, cut) =
  let solutions = interpret prog goal ([], False)
      values = [resolve soln template | (soln, _) <- solutions]
      listTerm = foldr (\v acc -> Func "." [v, acc]) (Atom "[]") values
  in case unify listTerm resultList of
       Nothing -> []
       Just sub' -> [(mergeSubst subst sub', cut)]
  where
    resolve s t
      | t' == t    = t
      | otherwise  = resolve s t'
      where t' = substituteAll s t
interpret prog (Func "bagof" [template, goal, resultList]) (subst, cut) =
  let solutions = interpret prog goal ([], False)
  in if null solutions then [] else
       let values = [resolve soln template | (soln, _) <- solutions]
           listTerm = foldr (\v acc -> Func "." [v, acc]) (Atom "[]") values
       in case unify listTerm resultList of
            Nothing -> []
            Just sub' -> [(mergeSubst subst sub', cut)]
  where
    resolve s t
      | t' == t    = t
      | otherwise  = resolve s t'
      where t' = substituteAll s t
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
