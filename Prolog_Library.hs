-- Ari Vitor da Silva Lazzarotto

--1 - Interpretar com Ghci:
--2 - Digitar "main" e apertar enter no interpretador:
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

data Term = Var String | Atom String | Func String [Term] | Term :|| Term
       deriving (Eq,Show)
data Clause = Term :- [Term] | Simple Term | Term :\== Term
       deriving (Eq,Show)

type Prolog = [Clause]

--unification https://www.javatpoint.com/unification-in-prolog
--prolog in haskell https://core.ac.uk/download/pdf/84872478.pdf e tbm https://github.com/aartamonau/hswip
--o Prolog tenta combinar o objetivo com cada cláusula. O processo de correspondência funciona da esquerda para a direita. 
--A meta falhará se nenhuma correspondência for encontrada. Se uma correspondência for encontrada, a ação será executada. 
--O Prolog usa a técnica de unificação que é uma forma muito geral da técnica de correspondência. Na unificação, 
--uma ou mais variáveis ​​recebem valor para tornar os dois termos de chamada idênticos. Esse processo é chamado de vinculação das variáveis ​​aos valores. 
--Por exemplo, o Prolog pode unificar os termos cat(A) e cat(mary) ligando a variável A ao átomo mary, o que significa que estamos dando o valor mary à variável A. 
--O Prolog pode unificar pessoa(Kevin, dane) e pessoa(L , S) ligando L e S ao átomo de kevin e dane, respectivamente. Na partida, todas as variáveis ​​não têm valor. 
--Na unificação, uma vez que uma variável é vinculada ao valor, ela pode ser desvinculada novamente e talvez ser vinculada a um novo valor usando o retrocesso.

--unify :: Term -> Term -> Term
--unify (Var x) (Var y) = Var (if x == y then x->-Var y else )
--unify (Atom x) (Atom y) = Atom (if x == y then x->-Atom y else )
--unify (Func x xs) (Func y ys) = Func (if x == y then x->-Func y ys else )

preUnify :: Term -> Term -> Bool
preUnify _ _ = False
preUnify (Atom x) (Atom y) = x == y
preUnify (Var x) (Var y) = x == y
preUnify (Var x) (Atom y) = True
preUnify (Atom x) (Var y) = True
--preUnify (x:xs) (y:ys) = preUnify x y && preUnify xs ys

canUnify :: Clause -> Clause -> Bool
canUnify _ _ = False
canUnify (Simple (Func y (x:xs))) (Simple (Func z (w:ws))) = (y == z && preUnify x w) && canUnify (Simple (Func y xs)) (Simple (Func z ws))

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

       --Sorted is a sorted version of List if Sorted is
       --a permutation of List (same elements in possibly
       --different order) and Sorted is sorted (second rule).
myProg2 :: Prolog
myProg2 = [
       --A list is sorted if it has zero or one elements,
       --or if it has two or more and they are in the
       --right order (recursively).
       Simple (Func "sorted" []),
       Simple (Func "sorted" [Var "_"]),
       Func "sorted" [Var "X", Var "Y" :|| Var "Rest"] :- [Func "menorIgual" [Var "X", Var "Y"], Func "sorted" [Var "Y" :|| Var "Rest"]],
       Func "sorted" [Var "List", Var "Sorted"] :- [Func "perm" [Var "List", Var "Sorted"], Func "sorted" [Var "Sorted"]],

       --A permutation of a list is one of the elements
       --of the original list stuck at the head of the
       --permuted list, and the rest is a permuted version
       --of the original list without that element.
       Simple (Func "perm" []),
       Func "perm" [Var "List", Var "H" :|| Var "Perm"] :- [Func "delete" [Var "H", Var "List", Var "Rest"], Func "perm" [Var "Rest", Var "Perm"]],

       --Delete an element from a list by just not including
       --t when it's found (recursively; like the member rule).
       Simple (Func "delete" [Var "X", Var "X" :|| Var "T", Var "T"]),
       Func "delete" [Var "X", Var "H" :|| Var "T", Var "H" :|| Var "NT"] :- [Func "delete" [Var "X", Var "T", Var "NT"]]]

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