{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

import Data.Maybe (mapMaybe)

data Term = Var String | Atom String | Func String [Term]
       deriving (Eq,Show)
data Clause = Term :- [Term] | Simple Term
       deriving (Eq,Show)

type Prolog = [Clause]
type Subst = Maybe [(String, Term)]

main :: IO ()
main = do
       example
       example1
       example2

example :: IO ()
example = print (queryResult myExample (Func "mae" [Var "Y", Atom "ari_vitor"]))     

example1 :: IO ()
example1 = print (queryResult myExample (Func "pai" [Var "Q", Atom "janeti"])) 

example2 :: IO ()
example2 = print (queryResult myExample (Func "mae" [Var "X", Atom "ari"])) 

       --Genealogic Tree example
myExample :: Prolog
myExample = [              
       Simple (Func "progenitor" [Atom "joao", Atom "ari"]),
       Simple (Func "progenitor" [Atom "vitoria", Atom "ari"]),
       Simple (Func "progenitor" [Atom "paulina", Atom "janeti"]),
       Simple (Func "progenitor" [Atom "olicio", Atom "janeti"]),
       Simple (Func "progenitor" [Atom "janeti", Atom "ari_vitor"]),
       Simple (Func "progenitor" [Atom "ari", Atom "ari_vitor"]),
       Simple (Func "progenitor" [Atom "ari", Atom "ariel"]),
       Simple (Func "progenitor" [Atom "janeti", Atom "ariel"]),
       Simple (Func "sexo" [Atom "paulina", Atom "feminino"]),
       Simple (Func "sexo" [Atom "vitoria", Atom "feminino"]),
       Simple (Func "sexo" [Atom "janeti", Atom "feminino"]),
       Simple (Func "sexo" [Atom "ari", Atom "masculino"]),
       Simple (Func "sexo" [Atom "joao", Atom "masculino"]),
       Simple (Func "sexo" [Atom "olicio", Atom "masculino"]),
       Simple (Func "sexo" [Atom "ari_vitor", Atom "masculino"]),
       Simple (Func "sexo" [Atom "ariel", Atom "masculino"]),
               Func "mae" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "Y"], Func "sexo" [Var "X", Atom "feminino"]],
               Func "pai" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "Y"], Func "sexo" [Var "X", Atom "masculino"]]]

-- Retorna o resultado da consulta.
queryResult :: Prolog -> Term -> [(String, String)]
queryResult prog term = case interpret prog (renamed term) of
       Nothing -> []
       Just solution -> undoRenamed (filterVars (result (Just solution)) (varsInTerm (renamed term)))
       where
              filterVars result vars = [(x, t) | (x, t) <- result, x `elem` vars]                                    --Remove as variáveis que não estão na consulta.
              varsInTerm (Atom _) = []
              varsInTerm (Var x) = [x]
              varsInTerm (Func _ args) = concatMap varsInTerm args
              renamed (Func n args) = Func n (map renamed args)
              renamed (Var x) = Var (x ++ "øVAR")
              renamed (Atom x) = Atom x
              undoRenamed xs = [(takeWhile (/= 'ø') x, t) | (x, t) <- xs]                                            --Desfaz a conversão alfa para exibir pro usuário.
              result Nothing = []
              result (Just subst) = case subst of
                     [] -> []
                     ((x,t):rest) -> if hasTooManyOccurrences subst then (x, extractAtom (substituteAll [(x, t)] (Var x))) : extractSubst rest else [(x, extractAtom (substituteAll subst (Var x))) | (x, _) <- subst]
                            where
                                   extractAtom (Atom x) = x
                                   extractSubst [] = []
                                   extractSubst ((x, t):rest) = (x, extractAtom (substituteAll [(x, t)] (Var x))) : extractSubst rest
                                   hasTooManyOccurrences list = length (filter (\(x, t) -> x == fst (head list)) list) > 1

-- Retorna as substituições realizadas para o termo consultado ser unificado.
interpret :: Prolog -> Term -> Subst
interpret prog term = let substs = mapMaybe (interpretClause term) query
       in case substs of
              [] -> Nothing
              _ -> Just (concat substs)
       where
              headOf (t :- _) = t
              headOf (Simple t) = t
              bodyOf (t :- ts) = ts
              bodyOf (Simple t) = []
              query = [clause | clause <- prog, match term (headOf clause)]
                     where
                            match (Atom x) (Atom y) = x == y
                            match (Var x) _ = True
                            match _ (Var x) = True
                            match (Func n1 args1) (Func n2 args2) = n1 == n2 && length args1 == length args2 && all (uncurry match) (zip args1 args2)
              interpretClause t c = case unify (headOf c) t of
                     Nothing -> Nothing
                     Just subst -> case interpretBody (map (substituteAll subst) (bodyOf c)) of
                            Nothing -> interpret (tail prog) t
                            Just subst' -> Just (subst ++ subst')
                     where
                            interpretBody [] = Just []
                            interpretBody (t:ts) = case interpret prog t of
                                   Nothing -> Nothing
                                   Just subst'' -> case interpretBody (map (substituteAll subst'') ts) of
                                          Nothing -> Nothing
                                          Just subst''' -> Just (subst'' ++ subst''')

-- Retorna uma lista de substituições a serem realizadas para que dois termos sejam unificados.
unify :: Term -> Term -> Subst
unify (Atom x) (Atom y) = if x == y then Just [] else Nothing
unify term (Var x) = Just [(x, term)]
unify (Var x) term = unify term (Var x)
unify (Func n1 args1) (Func n2 args2) = if n1 == n2 && length args1 == length args2 then unifyList args1 args2 else Nothing
       where
              unifyList [] [] = Just []
              unifyList (t:ts) (t':ts') = case unify t t' of
                     Nothing -> Nothing
                     Just subst -> case unifyList (map (substituteAll subst) ts) (map (substituteAll subst) ts') of
                            Nothing -> Nothing
                            Just subst' -> Just (subst ++ subst')

-- Recebe uma lista de substituições e o termo onde as substituições serão realizadas e retorna o termo com as substituições realizadas.
substituteAll :: [(String, Term)] -> Term -> Term
substituteAll [] term = term
substituteAll ((x, t):xs) t' = substituteAll xs (substitute (x, t) t')
       where
              substitute (x, t) (Atom y) = Atom y
              substitute (x, t) (Var y) = if x == y then t else Var y
              substitute (x, t) (Func n args) = Func n (map (substitute (x, t)) args)