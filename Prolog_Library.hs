{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

import Data.List (nub)

-- Ari Vitor da Silva Lazzarotto

--1 - Interpretar com Ghci:
--2 - Digitar "main" e apertar enter no interpretador:

data Term = Var String | Atom String | Func String [Term] | Term :\== Term          -- :\== necessita ser adicionado em match e unify para que o programa funcione corretamente.
       deriving (Eq,Show)
data Clause = Term :- [Term] | Simple Term
       deriving (Eq,Show)

type Prolog = [Clause]
type Subst = Maybe [(String, Term)]

-- Retorna a cabeça de uma cláusula
headOf :: Clause -> Term
headOf (t :- _) = t
headOf (Simple t) = t

-- Retorna o corpo de uma cláusula
bodyOf :: Clause -> [Term]
bodyOf (t :- ts) = ts
bodyOf (Simple t) = []

-- Verifica se dois termos unificam
match :: Term -> Term -> Bool
match (Atom x) (Atom y) = x == y
match (Var x) _ = True
match _ (Var x) = True
match (Var t :\== Var t') _ = False
match (Func n1 args1) (Func n2 args2) = n1 == n2 && length args1 == length args2 && all (uncurry match) (zip args1 args2)          --Verifica se é a mesma função e se os argumentos podem ser unificados.                       
match _ _ = False

-- Substitui variáveis em um termo
substitute :: (String, Term) -> Term -> Term
substitute (x, t) (Var y) = if x == y then t else Var y                                             --Se a variável for igual a x, retorna o termo t, senão retorna a variável.
substitute (x, t) (Atom y) = Atom y
substitute (x, t) (Func n args) = Func n (map (substitute (x, t)) args)                             --Aplica a substituição em toda a lista de argumentos.
substitute (x, t) (Var a :\== Var b) = if x == a then Var b :\== Var b else Var a :\== Var b        --Substitui a variável em uma expressão de desigualdade.

substituteAll :: [(String, Term)] -> Term -> Term
substituteAll [] t = t
substituteAll ((x, t):xs) t' = substituteAll xs (substitute (x, t) t')                              --Aplica a substituição em todos os termos da lista.

-- Gera uma lista de variáveis que não estão na lista de variáveis usadas
freshVars :: [String] -> [String]
freshVars usedVars = [name | i <- [1..], let name = "VAR" ++ show i, name `notElem` usedVars]       --Pode vir a causar problemas se o número de variáveis for muito grande(overhead).

-- Retorna todas as variáveis em um termo
vars :: Term -> [String]
vars (Var x) = [x]
vars (Atom _) = []
vars (Func _ args) = nub $ concatMap vars args
vars (t :\== t') = nub $ vars t ++ vars t'

-- Retorna todas as substituições que unificam com um termo
unify :: Term -> Term -> Subst
unify (Atom x) (Atom y) = if x == y then Just [] else Nothing                                        --Se forem átomos, verifica se são iguais e retorna a substituição vazia.
unify (Var x) (Atom y) = Just [(x, Atom y)]                                                          --Se forem uma variável e um átomo, retorna a substituição.
unify (Atom x) (Var y) = Just [(y, Atom x)]                                                          --Se forem um átomo e uma variável, retorna a substituição.
unify (Var x) (Var y) = Just [(x, Var y)]                                                            --Se forem variáveis, retorna a substituição, pois variaveis sempre podem ser unificadas.
unify (Var t :\== Var t') _ = if t == t' then Just [] else Nothing
unify t (Var x) = unify (Var x) t
unify (Var x) t
       | x `notElem` vars t = Just [(x, t)]                                                          --Se x não estiver em t, retorna a substituição.
       | otherwise = case freshVars (vars t) of                                                      --Se x já estiver em t, gera um novo nome de variável antes.
              [] -> Nothing 
              (y:_) -> Just [(y, t)]                                                                 --Usa o novo nome de variável para substituir x em t.
unify (Func n1 args1) (Func n2 args2) = if n1 == n2 && length args1 == length args2 then unifyList args1 args2 else Nothing--Se as funções tiverem o mesmo nomee o mesmo número de argumentos, tenta unificar as listas de argumentos.
unify _ _ = Nothing

unifyList :: [Term] -> [Term] -> Subst
unifyList [] [] = Just []
unifyList (t:ts) (t':ts') = case unify t t' of
       Nothing -> Nothing
       Just subst -> case unifyList (map (substituteAll subst) ts) (map (substituteAll subst) ts') of
              Nothing -> Nothing
              Just subst' -> Just (subst ++ subst')
unifyList _ _ = Nothing

-- Interpreta o programa, percorre cada cláusula do programa e gera uma lista de substituições a serem realizadas.
interpret :: Prolog -> Term -> Subst
interpret prog term = case unify (headOf clause) term of                                              --Unifica a cabeça da cláusula com o termo.
       Nothing -> Nothing
       Just subst -> case interpretList prog (map (substituteAll subst) (bodyOf clause)) of           --Caso unifique, aplica a substituição no corpo da cláusula.
              Nothing -> Nothing
              Just subst' -> Just (subst ++ subst')
       where clause = head (query prog term)                                                          --Busca a primeira cláusula que unifica com o termo.
             query prog term = [clause | clause <- prog, match term (headOf clause)]                  --Verifica se a cabeça da cláusula? unifica com o termo para toda cláusula do programa e retorna a lista de cláusulas que unificam com o termo - -- busca cláusulas que unificam com um termo. unify (headOf (head (query myExample3 (Func "irmao" [Var "X", Atom "ariel"])))) (Func "irmao" [Var "X", Atom "ariel"])

interpretList :: Prolog -> [Term] -> Subst
interpretList _ [] = Just []
interpretList prog (t:ts) = case interpret prog t of
       Nothing -> Nothing
       Just subst -> case interpretList prog (map (substituteAll subst) ts) of
              Nothing -> Nothing
              Just subst' -> Just (subst ++ subst')

-- Aplica a substituição em todas as variáveis da lista subst
result :: Subst -> [Term]
result Nothing = []
result (Just subst) = [substituteAll subst (Var x) | (x, _) <- subst]                                --Aplica a substituição em todas as variáveis da lista subst.

-- Retorna o resultado da consulta
queryResult :: Prolog -> Term -> [Term]
queryResult prog term = case interpret prog term of 
       Nothing -> []                                        
       Just subst -> [head (result (Just subst))]

main1 :: IO ()
main1 = print (queryResult myExample1 (Func "parent" [Var "X", Atom "koos"]))

main2 :: IO ()
main2 = print (queryResult myExample2 (Func "likes" [Var "X", Atom "prolog"]))

main3 :: IO ()
main3 = print (queryResult myExample3 (Func "irmao" [Var "X", Atom "ariel"]))

--Examples

       --Modern Compiler Design Example page 613
myExample1 :: Prolog
myExample1 = [
       Simple (Func "parent" [Atom "arne", Atom "james"]),
       Simple (Func "parent" [Atom "arne", Atom "sachiko"]),
       Simple (Func "parent" [Atom "koos", Atom "rivka"]),
       Simple (Func "parent" [Atom "sachiko", Atom "rivka"]),
       Simple (Func "parent" [Atom "truitje", Atom "koos"])]

       --Maribel Example page 171
myExample2 :: Prolog
myExample2 = [
       Simple (Func "based" [Atom "prolog", Atom "logic"]),
       Simple (Func "based" [Atom "haskell", Atom "maths"]),
       Simple (Func "likes" [Atom "max", Atom "logic"]),
       Simple (Func "likes" [Atom "claire", Atom "maths"]),
       Func "likes" [Var "X", Var "P"] :- [Func "based" [Var "P", Var "Y"], Func "likes" [Var "X", Var "Y"]]] 

       --Genealogic Tree Example --- olhar maribel, tudo que era x, vira Z, nas substituições
myExample3 :: Prolog
myExample3 = [
       Simple (Func "progenitor" [Atom "vitoria", Atom "joao"]),
       Simple (Func "progenitor" [Atom "olicio", Atom "joao"]),
       Simple (Func "progenitor" [Atom "vitoria", Atom "paulina"]),
       Simple (Func "progenitor" [Atom "olicio", Atom "paulina"]),
       Simple (Func "progenitor" [Atom "joao", Atom "ari"]),
       Simple (Func "progenitor" [Atom "vitoria", Atom "ari"]),
       Simple (Func "progenitor" [Atom "olicio", Atom "janeti"]),
       Simple (Func "progenitor" [Atom "paulina", Atom "janeti"]),
       Simple (Func "progenitor" [Atom "ari", Atom "ari_vitor"]),
       Simple (Func "progenitor" [Atom "janeti", Atom "ari_vitor"]),
       Simple (Func "progenitor" [Atom "ari", Atom "ariel"]),
       Simple (Func "progenitor" [Atom "janeti", Atom "ariel"]),
       Simple (Func "sexo" [Atom "paulina", Atom "feminino"]),
       Simple (Func "sexo" [Atom "vitoria", Atom "feminino"]),
       Simple (Func "sexo" [Atom "janeti", Atom "feminino"]),
       Simple (Func "sexo" [Atom "ari", Atom "masculino"]),
       Simple (Func "sexo" [Atom "joao", Atom "masculino"]),
       Simple (Func "sexo" [Atom "olicio", Atom "masculino"]),
       Simple (Func "sexo" [Atom "ariel", Atom "masculino"]),
       Simple (Func "sexo" [Atom "ari_vitor", Atom "masculino"]),
              Func "irma" [Var "X", Var "Y"] :- [Func "progenitor" [Var "A", Var "X"], Func "progenitor" [Var "A", Var "Y"], Var "X" :\== Var "Y", Func "sexo" [Var "X", Atom "feminino"]],
             Func "irmao" [Var "X", Var "Y"] :- [Func "progenitor" [Var "A", Var "X"], Func "progenitor" [Var "A", Var "Y"], Var "X" :\== Var "Y", Func "sexo" [Var "X", Atom "masculino"]],
       Func "descendente" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "Y"]],
       Func "descendente" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "A"], Func "descendente" [Var "A", Var "Y"]],
               Func "avo" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "A"], Func "progenitor" [Var "A", Var "Y"], Func "sexo" [Var "X", Atom "masculino"]],
               Func "mae" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "Y"], Func "sexo" [Var "X", Atom "feminino"]],
               Func "pai" [Var "X", Var "Y"] :- [Func "progenitor" [Var "X", Var "Y"], Func "sexo" [Var "X", Atom "masculino"]],
               Func "tio" [Var "X", Var "Y"] :- [Func "irmao" [Var "X", Var "A"], Func "progenitor" [Var "A", Var "Y"]],
             Func "primo" [Var "X", Var "Y"] :- [Func "irmao" [Var "A", Var "B"], Func "progenitor" [Var "A", Var "X"], Func "progenitor" [Var "B", Var "Y"], Var "X" :\== Var "Y"],
             Func "primo" [Var "X", Var "Y"] :- [Func "irma" [Var "A", Var "B"], Func "progenitor" [Var "A", Var "X"], Func "progenitor" [Var "B", Var "Y"], Var "X" :\== Var "Y"]]