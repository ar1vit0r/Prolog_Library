{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

-- Ari Vitor da Silva Lazzarotto

--1 - Interpretar com Ghci:
--2 - Digitar "main" e apertar enter no interpretador:

import qualified Data.Maybe --Data.Maybe -> https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Maybe.html
                            --Nothing serve para representar um valor que não existe (não é um valor válido) e Just x serve para representar um valor que existe (é um valor válido). 
                            --Funciona como um tipo de dado que pode ser Nothing ou Just x, onde x é um valor válido.           

data Term = Var String | Atom String | Func String [Term]
       deriving (Eq,Show)
data Clause = Term :- [Term] | Simple Term | Term :\== Term
       deriving (Eq,Show)

type Prolog = [Clause]

-- Função que retorna a cabeça de uma cláusula
headOf :: Clause -> Term
headOf (t :- _) = t
headOf (Simple t) = t
headOf (t :\== _) = t

-- Função que retorna o corpo de uma cláusula
bodyOf :: Clause -> [Term]
bodyOf (t :- ts) = ts       
bodyOf (Simple t) = []
bodyOf (t :\== t') = []

-- Função que verifica se dois termos unificam
match :: Term -> Term -> Bool
match (Var x) _ = True
match _ (Var x) = True
match (Atom x) (Atom y) = x == y
match (Func n1 args1) (Func n2 args2) = n1 == n2 && all (uncurry match) (zip args1 args2)           --Verifica se os nomes são iguais e se os argumentos unificam
match _ _ = False

-- Função que busca cláusulas que unificam com um termo - query myProg1 (Atom "prolog")
query :: Prolog -> Term -> [Clause]
query prog term = [clause | clause <- prog, match term (headOf clause)]                             --Busca todas as cláusulas que unificam com o termo

-- Função que substitui variáveis em um termo
substitute :: (String, Term) -> Term -> Term
substitute (x, t) (Var y) = if x == y then t else Var y                                             --Se a variável for igual a x, retorna o termo t, senão retorna a variável
substitute (x, t) (Atom y) = Atom y
substitute (x, t) (Func n args) = Func n (map (substitute (x, t)) args)                             --Aplica a substituição em todos os argumentos

-- Função que substitui variáveis em uma lista de termos
substituteAll :: [(String, Term)] -> Term -> Term
substituteAll [] t = t
substituteAll ((x, t):xs) t' = substituteAll xs (substitute (x, t) t')                              --Aplica a substituição em todos os termos da lista

-- Função que aplica uma substituição em uma cláusula
applySubst :: (String, Term) -> Clause -> Clause
applySubst (x, t) (t1 :- ts) = substitute (x, t) t1 :- map (substitute (x, t)) ts                   --Aplica a substituição na cabeça e no corpo
applySubst (x, t) (Simple t1) = Simple (substitute (x, t) t1)                                       --Aplica a substituição no termo
applySubst (x, t) (t1 :\== t2) = substitute (x, t) t1 :\== substitute (x, t) t2                     --Aplica a substituição nos dois termos

-- Função que retorna todas as substituições que unificam com um termo
unify :: Term -> Term -> Maybe [(String, Term)]
unify (Var x) t = Just [(x, t)]
unify t (Var x) = Just [(x, t)]
unify (Atom x) (Atom y) = if x == y then Just [] else Nothing                                        --Se os átomos forem iguais, retorna uma lista vazia
unify (Func n1 args1) (Func n2 args2) = if n1 == n2 then unifyList args1 args2 else Nothing          --Se os nomes forem iguais, unifica as listas de argumentos
unify _ _ = Nothing                                                                                  

-- Função que retorna todas as substituições que unificam com uma lista de termos
unifyList :: [Term] -> [Term] -> Maybe [(String, Term)]
unifyList [] [] = Just []
unifyList (t:ts) (t':ts') = case unify t t' of                                                        --Unifica os termos da lista
       Nothing -> Nothing                                                                             --Se não unificou, retorna Nothing
       Just subst -> case unifyList (map (substituteAll subst) ts) (map (substituteAll subst) ts') of --Se unificou, aplica a substituição e continua
              Nothing -> Nothing
              Just subst' -> Just (subst ++ subst')                                                   --Concatena as substituições
unifyList _ _ = Nothing

--Função que interpreta uma clausula
interpret :: Prolog -> Term -> Maybe [(String, Term)]
interpret prog term = case unify (headOf clause) term of                                              --Unifica a cabeça da cláusula com o termo
       Nothing -> Nothing
       Just subst -> case interpretList prog (map (substituteAll subst) (bodyOf clause)) of           --Aplica a substituição no corpo da cláusula e interpreta a lista
              Nothing -> Nothing
              Just subst' -> Just (subst ++ subst')                                                   --Concatena as substituições
       where clause = head (query prog term)                                                          --Busca a primeira cláusula que unifica com o termo

-- Função que interpreta uma lista de cláusulas
interpretList :: Prolog -> [Term] -> Maybe [(String, Term)]
interpretList _ [] = Just []
interpretList prog (t:ts) = case interpret prog t of                                                  --Interpreta o termo
       Nothing -> Nothing
       Just subst -> case interpretList prog (map (substituteAll subst) ts) of                        --Aplica a substituição e continua
              Nothing -> Nothing
              Just subst' -> Just (subst ++ subst')                                                   --Concatena as substituições                                   

main :: IO ()
main = print (interpret myProg1 (Func "likes" [Atom "max", Var "X"]))                                 --Busca todas as cláusulas que unificam com likes(max, X)

--Examples

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

myProg2 :: Prolog
myProg2 = [
       Simple (Func "parent" [Var "A", Var "B", Var "C"]),
       Simple (Func "parent" [Atom "kevin", Atom "henry", Atom "30"])]

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
       Var "X":\== Var "Y",
       Simple (Func "sexo" [Var "X", Atom "feminino"]),
--irmao
       Simple (Func "irmao" [Var "X", Var "Y"]),
       Simple (Func "progenitor" [Var "A", Var "X"]),
       Simple (Func "progenitor" [Var "A", Var "Y"]),
       Var "X":\== Var "Y",
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
       Var "X":\== Var "Y",
--primo
       Simple (Func "primo" [Var "X", Var "Y"]),
       Simple (Func "irma" [Var "A", Var "B"]),
       Simple (Func "progenitor" [Var "A", Var "X"]),
       Simple (Func "progenitor" [Var "B", Var "Y"]),
       Var "X":\== Var "Y"]
