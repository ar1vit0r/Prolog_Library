module Unify
       ( unify
       , substituteAll
       , varsInTerm
       , mergeSubst
       ) where

import Term

unify :: Term -> Term -> Maybe Subst
unify (Atom x) (Atom y)
  | x == y    = Just []
  | otherwise = Nothing
unify term (Var x) = Just [(x, term)]
unify (Var x) term = unify term (Var x)
unify Cut Cut = Just []
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
unify _ _ = Nothing

substituteAll :: Subst -> Term -> Term
substituteAll [] term = term
substituteAll ((x, t):xs) t' = substituteAll xs (sub (x, t) t')
  where
    sub _ Cut = Cut
    sub _ (Atom y) = Atom y
    sub (v, term) (Var y)
      | v == y    = term
      | otherwise = Var y
    sub s (Func n args) = Func n (map (sub s) args)
    sub s (Not nt) = Not (sub s nt)

varsInTerm :: Term -> [String]
varsInTerm Cut          = []
varsInTerm (Atom _)     = []
varsInTerm (Var x)      = [x]
varsInTerm (Func _ args) = concatMap varsInTerm args
varsInTerm (Not t)      = varsInTerm t

mergeSubst :: Subst -> Subst -> Subst
mergeSubst old new = [(v, substituteAll old t) | (v, t) <- new]
                     ++ [(v, substituteAll new t) | (v, t) <- old, not (any (\(v', _) -> v == v') new)]
