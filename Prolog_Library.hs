{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

import Language.Haskell.TH (match, ExpQ)  -- dyn -> Dynamically binding a variable (unhygenic)  
                                          --match -> https://hackage.haskell.org/package/template-haskell-2.16.0.0/docs/Language-Haskell-TH-Lib-Internal.html#v:match
-- Ari Vitor da Silva Lazzarotto

--1 - Interpretar com Ghci:
--2 - Digitar "main" e apertar enter no interpretador:

data Term = Var String | Atom String | Func String [Term]
       deriving (Eq,Show)
data Clause = Term :- [Term] | Simple Term | Term :\== Term
       deriving (Eq,Show)

type Prolog = [Clause]

subs:: (Term,Term) -> Term -> Term
subs (Var n1, t) (Var n2)
   | n1 == n2   = t
   | otherwise = Var n2
subs (t1,t2) (Atom s) = Atom s
subs (t1,t2) (Func n l) = Func n l'
   where l' = map (subs (t1,t2)) l --(map (subs (t1,t2) l)) -> substitui t1 por t2 em cada elemento da lista l

subsAll :: [(Term,Term)] -> Term -> Term
subsAll xs t = foldl (flip subs) t xs --subsAll (x:xs) t = subsAll xs (subs x t)

unify :: Term -> Clause -> [(Term,Term)]
unify t (Simple t2) = unify2 t t2
unify t (h :- t2) = unify2 t h

unify2 :: Term -> Term -> [(Term, Term)] --problem
unify2 (Func n1 l1) (Func n2 l2) = zip l1 l2
unify2 t1 t2 = []

canUnify :: Term -> Clause -> Bool -- canUnify (Func "parent" [Var "A", Var "B", Var "C"]) test10
canUnify t (Simple t2) = canUnify2 t t2
canUnify t (h :- t2) = canUnify2 t h

canUnify2 :: Term -> Term -> Bool
canUnify2 (Func n1 l1) (Func n2 l2)
    | n1 == n2    = canUnifyArgs l1 l2
canUnify2 (Atom n1) (Atom n2) = n1 == n2

canUnifyArgs :: [Term] -> [Term] -> Bool --canUnifyArgs ([Var "A", Var "B", Var "C"]) ([Atom "kevin", Atom "henry", Atom "30"])
canUnifyArgs [] [] = True
canUnifyArgs ((Var n1):xs) ((Var n2):ys) =  canUnifyArgs xs ys
canUnifyArgs ((Atom n1):xs) ((Atom n2):ys) =  n1 == n2 && canUnifyArgs xs ys
canUnifyArgs ((Atom n1):xs) ((Var n2):ys) =  canUnifyArgs xs ys
canUnifyArgs (_:xs) (_:ys)  = False

--https://curiosity-driven.org/prolog-interpreter

--o Prolog tenta combinar o objetivo com cada cláusula. O processo de correspondência funciona da esquerda para a direita. 
--A meta falhará se nenhuma correspondência for encontrada. Se uma correspondência for encontrada, a ação será executada. 
--O Prolog usa a técnica de unificação que é uma forma muito geral da técnica de correspondência. Na unificação, 
--uma ou mais variáveis ​​recebem valor para tornar os dois termos de chamada idênticos. Esse processo é chamado de vinculação das variáveis ​​aos valores. 
--Por exemplo, o Prolog pode unificar os termos cat(A) e cat(mary) ligando a variável A ao átomo mary, o que significa que estamos dando o valor mary à variável A. 
--O Prolog pode unificar pessoa(Kevin, dane) e pessoa(L , S) ligando L e S ao átomo de kevin e dane, respectivamente. Na partida, todas as variáveis ​​não têm valor. 
--Na unificação, uma vez que uma variável é vinculada ao valor, ela pode ser desvinculada novamente e talvez ser vinculada a um novo valor usando o retrocesso.

--https://www.educative.io/answers/what-is-the-match-method-javascript
--an expression that needs to be searched or replaced and a modifier that modifies the search
--match :: 

--substitute — that takes variable bindings from match and returns a term with all occurrences of these 
--variables substituted with values from the bindings map.
--subs :: (Var, Term) -> Term -> Term  
--subst ::[(Var,Term)] -> Term -> Term

--This function takes two maps of bindings and returns a combined bindings map if there are no conflicts. 
--If any of the bound variables is present in both bindings maps but the terms they are bound to do not match then mergeBindings returns null.
--mergeBindings :: [(Var,Term)] -> [(Var,Term)] -> [(Var,Term)]

       -- parent(A, B, C)  Unify parent(kevin, henry, 30) 
test1 :: Clause
test1 = Simple (Func "parent" [Var "A", Var "B", Var "C"])

test10 :: Clause
test10 = Simple (Func "parent" [Atom "kevin", Atom "henry", Atom "30"])

       --Maribel Example page 171
myProg1 :: Prolog
myProg1 = [
       Simple (Func "based" [Atom "prolog", Atom "logic"]),
       Simple (Func "based" [Atom "haskell", Atom "maths"]),
       Simple (Func "likes" [Atom "max", Atom "logic"]),
       Simple (Func "likes" [Atom "claire", Atom "maths"]),
       Func "likes" [Var "X", Var "P"] :- [Func "based" [Var "P", Var "Y"], Func "likes" [Var "X", Var "Y"]]]

       --Genealogic Tree Example
myProg3 :: Prolog
myProg3 = [
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
--irma
       Simple (Func "irma" [Var "X", Var "Y"]),
       Simple (Func "progenitor" [Var "A", Var "X"]),
       Simple (Func "progenitor" [Var "A", Var "Y"]),
       Var "X":\== Var "Y", --X\==Y <-------------------
       Simple (Func "sexo" [Var "X", Atom "feminino"]),
--irmao
       Simple (Func "irmao" [Var "X", Var "Y"]),
       Simple (Func "progenitor" [Var "A", Var "X"]),
       Simple (Func "progenitor" [Var "A", Var "Y"]),
       Var "X":\== Var "Y", --X\==Y <-------------------
       Simple (Func "sexo" [Var "X", Atom "masculino"]),
--descendente
       Simple (Func "descendente" [Var "X", Var "Y"]),
       Simple (Func "progenitor" [Var "X", Var "Y"]),
       Simple (Func "descendente" [Var "X", Var "Y"]),
       Simple (Func "progenitor" [Var "X", Var "A"]),
       Simple (Func "descendente" [Var "A", Var "Y"]),
--avo
       Simple (Func "avo" [Var "X", Var "Y"]),
       Simple (Func "progenitor" [Var "X", Var "A"]),
       Simple (Func "progenitor" [Var "A", Var "Y"]),
       Simple (Func "sexo" [Var "X", Atom "masculino"]),
--mae
       Simple (Func "mae" [Var "X", Var "Y"]),
       Simple (Func "progenitor" [Var "X", Var "Y"]),
       Simple (Func "sexo" [Var "X", Atom "feminino"]),
--pai
       Simple (Func "pai" [Var "X", Var "Y"]),
       Simple (Func "progenitor" [Var "X", Var "Y"]),
       Simple (Func "sexo" [Var "X", Atom "masculino"]),
--tio
       Simple (Func "tio" [Var "X", Var "Y"]),
       Simple (Func "irmao" [Var "X", Var "A"]),
       Simple (Func "progenitor" [Var "A", Var "Y"]),
--primo
       Simple (Func "primo" [Var "X", Var "Y"]),
       Simple (Func "irmao" [Var "A", Var "B"]),
       Simple (Func "progenitor" [Var "A", Var "X"]),
       Simple (Func "progenitor" [Var "B", Var "Y"]),
       Var "X":\== Var "Y", --X\==Y <-------------------
--primo
       Simple (Func "primo" [Var "X", Var "Y"]),
       Simple (Func "irma" [Var "A", Var "B"]),
       Simple (Func "progenitor" [Var "A", Var "X"]),
       Simple (Func "progenitor" [Var "B", Var "Y"]),
       Var "X":\== Var "Y"] --X\==Y <-------------------
