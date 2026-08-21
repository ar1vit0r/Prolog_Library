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

renameTerm :: Term -> State Int Term
renameTerm (Atom x) = return (Atom x)
renameTerm (Var x) = do
  v <- freshVar
  return (Var (x ++ v))
renameTerm (Func n args) = do
  args' <- mapM renameTerm args
  return (Func n args')

queryResult :: Prolog -> Term -> [(String, String)]
queryResult prog term = case evalState (renameTerm term) 0 of
  renamed -> case interpret prog renamed ([], False) of
    Right (subst, _) -> undoRenamed
      [(x, extractAtom (substituteAll subst (Var x)))
       | (x, _) <- subst, x `elem` varsInTerm renamed]
    Left _ -> []
  where
    extractAtom (Atom x) = x
    extractAtom _        = ""
    undoRenamed xs = [(takeWhile (/= '_') x, t) | (x, t) <- xs, not (null t)]

interpret :: Prolog -> Term -> CutState -> PrologResult
interpret _ _ (subst, True) = Right (subst, True)
interpret prog term cs@(_, cut) = case filter (matches term . headOf) prog of
  [] -> Right ([], cut)
  clauses -> tryClauses clauses
  where
    headOf (t :- _)  = t
    headOf (Simple t) = t
    headOf Cut        = Atom ""

    matches (Atom x) (Atom y)   = x == y
    matches (Var _) _           = True
    matches _ (Var _)           = True
    matches (Func n1 a1) (Func n2 a2) =
      n1 == n2 && length a1 == length a2 && all (uncurry matches) (zip a1 a2)
    matches _ _                 = False

    tryClauses [] = Right ([], cut)
    tryClauses (c:rest) = case unify (headOf c) term of
      Nothing -> tryClauses rest
      Just sub -> case c of
        Simple _ -> Right (sub, cut)
        _ :- body -> case interpretBody prog (map (substituteAll sub) body) ([], False) of
          Right (bodySub, bodyCut) ->
            if bodyCut then Right (sub ++ bodySub, True)
            else Right (sub ++ bodySub, cut)
          Left err -> if cut then Left err else tryClauses rest
        Cut -> Right ([], True)

    interpretBody _ [] cs' = Right cs'
    interpretBody p (g:gs) (accSub, accCut) = case interpret p g (accSub, False) of
      Left err -> Left err
      Right (sub, subCut) ->
        let newSub = accSub ++ sub
            newCut = accCut || subCut
        in if subCut
           then interpretBody p gs (newSub, True)
           else interpretBody p gs (newSub, newCut)
