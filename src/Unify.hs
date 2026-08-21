module Unify
       ( unify
       , substituteAll
       , varsInTerm
       ) where

import Term

unify :: Term -> Term -> Maybe Subst
unify (Atom x) (Atom y)
  | x == y    = Just []
  | otherwise = Nothing
unify term (Var x) = Just [(x, term)]
unify (Var x) term = unify term (Var x)
unify (Func n1 args1) (Func n2 args2)
  | n1 == n2 && length args1 == length args2 = unifyList args1 args2
  | otherwise = Nothing
  where
    unifyList [] [] = Just []
    unifyList (t:ts) (t':ts') = case unify t t' of
      Nothing -> Nothing
      Just subst -> case unifyList (map (substituteAll subst) ts)
                                   (map (substituteAll subst) ts') of
        Nothing -> Nothing
        Just subst' -> Just (subst ++ subst')

substituteAll :: Subst -> Term -> Term
substituteAll [] term = term
substituteAll ((x, t):xs) t' = substituteAll xs (sub (x, t) t')
  where
    sub _ (Atom y) = Atom y
    sub (v, term) (Var y)
      | v == y    = term
      | otherwise = Var y
    sub s (Func n args) = Func n (map (sub s) args)

varsInTerm :: Term -> [String]
varsInTerm (Atom _)     = []
varsInTerm (Var x)      = [x]
varsInTerm (Func _ args) = concatMap varsInTerm args
