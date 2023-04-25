{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

import Data.List (nub, permutations) -- nub remove elementos duplicados de uma lista, permutations retorna todas as permutações de uma lista.

-- https://downloads.haskell.org/~ghc/7.2.1/docs/html/users_guide/pragmas.html - 7.13.5.1. INLINE pragma - GHC User's Guide

-- bug com a função mae e avo, porém pai funciona o.O (não sei o motivo) -- mae de janeti é a janeti? lul

data Term = Var String | Atom String | Func String [Term]
       deriving (Eq,Show)
data Clause = Term :- [Term] | Simple Term
       deriving (Eq,Show)

type Prolog = [Clause]
type Subst = Maybe [(String, Term)]

-- Retorna o resultado da consulta, caso não encontrar, tenta novamente para todas permutas da lista.
queryResult :: Prolog -> Term -> [Term]
queryResult prog term = case interpret prog (alphaConvert term) of
       Nothing -> case alphaConvert term of
              Func n xs -> case permutations xs of 
                     [] -> []
                     (x:xs) -> queryResultAux prog (Func n x) ++ queryResultAux prog (Func n (head xs))
              _ -> []
       Just solution -> [head (result (Just solution))]
       where
              alphaConvert (Func n args) = Func n (map alphaConvert args)
              alphaConvert (Var x) = Var (x ++ head [newName | i <- [1..], let newName = "!@#$%%^&*_+VAR" ++ show i] )
              alphaConvert (Atom x) = Atom x 
              result Nothing = []
              result (Just subst) = [substituteAll subst (Var x) | (x, _) <- subst]                                 --Desencapsula o Maybe e retorna o resultado.
              queryResultAux prog term = case interpret prog (alphaConvert term) of
                     Nothing -> []
                     Just subst -> [head (result (Just subst))]

-- Percorre cada cláusula que der match com o termo da consulta e aplica a unificação.
interpret :: Prolog -> Term -> Subst
interpret prog term = case query prog term of
       [] -> Nothing
       (clause:_) -> case unify (headOf clause) term of
              Nothing -> Nothing
              Just subst -> case interpretList prog (map (substituteAll subst) (bodyOf clause)) of
                     Nothing -> Nothing
                     Just subst' -> Just (subst ++ subst')
       where
              interpretList _ [] = Just []
              interpretList prog (t:ts) = case interpret prog t of                                                 --Percorre cada termo da lista de termos da cláusula e aplica a unificação com o termo da consulta
                     Nothing -> Nothing
                     Just subst -> case interpretList prog (map (substituteAll subst) ts) of
                            Nothing -> Nothing
                            Just subst' -> Just (subst ++ subst')
              headOf (t :- _) = t
              headOf (Simple t) = t
              bodyOf (t :- ts) = ts
              bodyOf (Simple t) = []
              query prog term = [clause | clause <- prog, match term (headOf clause)]
                     where
                            match (Atom x) (Atom y) = x == y
                            match (Var x) _ = True
                            match _ (Var x) = True
                            match (Func n1 args1) (Func n2 args2) = n1 == n2 && length args1 == length args2 && all (uncurry match) (zip args1 args2)--Verifica se é a mesma função e se os argumentos podem ser unificados.

-- Retorna uma lista de substituições a serem realizadas para que dois termos sejam unificados.
unify :: Term -> Term -> Subst
unify (Atom x) (Atom y) = if x == y then Just [] else Nothing
unify t (Var x) = Just [(x, t)]
unify (Var x) t = unify t (Var x)
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
substituteAll [] t = t
substituteAll ((x, t):xs) t' = substituteAll xs (substitute (x, t) t')                                            --Realiza uma lista de substituições em um termo.
       where
              substitute (x, t) (Atom y) = Atom y
              substitute (x, t) (Var y) = if x == y then t else Var y                                             --Se a variável for igual a x, retorna o termo t, senão retorna a variável.
              substitute (x, t) (Func n args) = Func n (map (substitute (x, t)) args)                             --Aplica a substituição em cada argumento da função.

------------------------------------------------------------------------
-- Exemplo de consulta interpretando o programa e exibindo o resultado--
------------------------------------------------------------------------

main :: IO ()
main = print (queryResult myExample (Func "mae" [Var "Q", Atom "janeti"]))              -- consulta pai funciona

main1 :: IO ()
main1 = print (queryResult myExample1 (Func "consulta" [Var "Q"]))

main2 :: IO ()
main2 = print (queryResult myExample2 (Func "parent" [Var "X", Atom "james"]))

main3 :: IO ()
main3 = print (queryResult myExample3 (Func "likes" [Atom "prolog", Var "Y"]))

--------------------------------
--Exemplo de programa Prolog----
--------------------------------

       --Genealogic Tree Example
myExample :: Prolog
myExample = [
       Simple (Func "progenitor" [Atom "joao", Atom "ari"]),
       Simple (Func "progenitor" [Atom "vitoria", Atom "ari"]),
       Simple (Func "progenitor" [Atom "olicio", Atom "janeti"]),
       Simple (Func "progenitor" [Atom "paulina", Atom "janeti"]),
       Simple (Func "progenitor" [Atom "ari", Atom "ari_vitor"]),
       Simple (Func "progenitor" [Atom "janeti", Atom "ari_vitor"]),
       Simple (Func "sexo" [Atom "paulina", Atom "feminino"]),
       Simple (Func "sexo" [Atom "vitoria", Atom "feminino"]),
       Simple (Func "sexo" [Atom "janeti", Atom "feminino"]),
       Simple (Func "sexo" [Atom "ari", Atom "masculino"]),
       Simple (Func "sexo" [Atom "joao", Atom "masculino"]),
       Simple (Func "sexo" [Atom "olicio", Atom "masculino"]),
       Simple (Func "sexo" [Atom "ari_vitor", Atom "masculino"]),
       Func "descendente" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "Y"]],
       Func "descendente" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "A"], Func "descendente" [Var "A", Var "Y"]],
               Func "avo" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "A"], Func "progenitor" [Var "A", Var "Y"], Func "sexo" [Var "X", Atom "masculino"]],
               Func "mae" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "Y"], Func "sexo" [Var "X", Atom "feminino"]],
               Func "pai" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "Y"], Func "sexo" [Var "X", Atom "masculino"]]]

myExample0 :: Prolog
myExample0 = [
       Simple (Func "progenitor" [Atom "joao", Atom "ari"]),
       Simple (Func "progenitor" [Atom "vitoria", Atom "ari"]),
       Simple (Func "progenitor" [Atom "olicio", Atom "janeti"]),
       Simple (Func "progenitor" [Atom "paulina", Atom "janeti"]),
       Simple (Func "progenitor" [Atom "ari", Atom "ari_vitor"]),
       Simple (Func "progenitor" [Atom "janeti", Atom "ari_vitor"]),
       Simple (Func "mulher" [Atom "paulina"]),
       Simple (Func "mulher" [Atom "vitoria"]),
       Simple (Func "mulher" [Atom "janeti"]),
       Simple (Func "homen" [Atom "ari"]),
       Simple (Func "homen" [Atom "joao"]),
       Simple (Func "homen" [Atom "olicio"]),
       Simple (Func "homen" [Atom "ari_vitor"]),
       Func "descendente" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "Y"]],
       Func "descendente" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "A"], Func "descendente" [Var "A", Var "Y"]],
               Func "avo" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "A"], Func "progenitor" [Var "A", Var "Y"], Func "homen" [Var "X"]],
               Func "mae" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "Y"], Func "mulher" [Var "X"]],
               Func "pai" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "Y"], Func "homen" [Var "X"]]]

myExample1 :: Prolog
myExample1 = [
       Simple (Func "irmao" [Atom "andre", Atom "joao"]),
       Func "consulta" [Var "X"] :- [Func "irmao" [Atom "andre", Var "X"]]]

       --Modern Compiler Design Example page 613
myExample2 :: Prolog
myExample2 = [
       Simple (Func "parent" [Atom "arne", Atom "james"]),
       Simple (Func "parent" [Atom "arne", Atom "sachiko"]),
       Simple (Func "parent" [Atom "koos", Atom "rivka"]),
       Simple (Func "parent" [Atom "sachiko", Atom "rivka"]),
       Simple (Func "parent" [Atom "truitje", Atom "koos"])]

       --Maribel Example page 171
myExample3 :: Prolog
myExample3 = [
       Simple (Func "based" [Atom "prolog", Atom "logic"]),
       Simple (Func "based" [Atom "haskell", Atom "maths"]),
       Simple (Func "likes" [Atom "max", Atom "logic"]),
       Simple (Func "likes" [Atom "claire", Atom "maths"]),
       Func "likes" [Var "X", Var "P"] :- [Func "based" [Var "P", Var "Y"], Func "likes" [Var "X", Var "Y"]]]

myExample4 :: Prolog
myExample4 = [
       Simple (Func "studies" [Atom "charlie", Atom "csc135"]),
       Simple (Func "studies" [Atom "olivia", Atom "csc135"]),
       Simple (Func "studies" [Atom "jack", Atom "csc131"]),
       Simple (Func "studies" [Atom "arthur", Atom "csc131"]),
       Simple (Func "teaches" [Atom "kirke", Atom "csc135"]),
       Simple (Func "teaches" [Atom "collins", Atom "csc131"]),
       Simple (Func "teaches" [Atom "collins", Atom "csc171"]),
       Simple (Func "teaches" [Atom "juniper", Atom "csc134"]),
       Func "professor" [Var "X", Var "Y"] :- [Func "teaches" [Var "X", Var "Z"], Func "studies" [Var "Y", Var "Z"]]]