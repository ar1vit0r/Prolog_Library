module Interpret
       ( queryResult
       , interpret
       ) where

import Control.Monad.State.Strict
import Term
import Unify

freshVar :: State Int String
freshVar = do
  n <- get
  put (n + 1)
  return ("_V" ++ show n)

renameWithMapping :: Term -> State Int (Term, [(String, String)])
renameWithMapping (Atom x) = return (Atom x, [])
renameWithMapping Cut = return (Cut, [])
renameWithMapping (Var x) = do
  v <- freshVar
  return (Var (x ++ v), [(x, x ++ v)])
renameWithMapping (Func n args) = do
  results <- mapM renameWithMapping args
  let args' = map fst results
      pairs = concatMap snd results
  return (Func n args', pairs)

queryResult :: Prolog -> Term -> [(String, String)]
queryResult prog term = case evalState (renameWithMapping term) 0 of
  (renamedTerm, mapping) ->
    let solutions = interpret prog renamedTerm ([], False)
    in case solutions of
         [] -> []
         (subst, _) : _ ->
           [(orig, val) | (orig, rn) <- mapping
           , let val = extractAtom (substituteAll subst (Var rn))
           , not (null val)]
  where
    extractAtom (Atom x) = x
    extractAtom _        = ""

interpret :: Prolog -> Term -> CutState -> [CutState]
interpret _ _ (subst, True) = [(subst, True)]
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
    matches _ _                   = False

    tryClause c = case unify (headOf c) term of
      Nothing -> []
      Just sub -> case c of
        Simple _ -> [(sub, False)]
        _ :- body ->
          let bodyGoals = map (substituteAll sub) body
              bodyResults = interpretBody prog bodyGoals ([], False)
          in [(mergeSubst sub bodySub, bodyCut) | (bodySub, bodyCut) <- bodyResults]

    interpretBody _ [] cs = [cs]
    interpretBody p (Cut:gs) (accSub, _) = interpretBody p gs (accSub, True)
    interpretBody p (g:gs) (accSub, accCut) =
      let gResults = interpret p g ([], False)
      in concatMap tryGoal gResults
      where
        tryGoal (sub, subCut) =
          let newSub = mergeSubst accSub sub
              newCut = accCut || subCut
              gs' = map (substituteAll sub) gs
          in if subCut
             then interpretBody p gs' (newSub, True)
             else interpretBody p gs' (newSub, newCut)
