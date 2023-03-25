{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

-- Ari Vitor da Silva Lazzarotto

--1 - Interpretar com Ghci:
--2 - Digitar "main" e apertar enter no interpretador:

data Term = Var String | Atom String | Func String [Term]
       deriving (Eq,Show)
data Clause = Term :- [Term] | Simple Term | Term :\== Term
       deriving (Eq,Show)

type Prolog = [Clause]

-- Retorna a cabeça de uma cláusula
headOf :: Clause -> Term
headOf (t :- _) = t
headOf (Simple t) = t
headOf (t :\== _) = t

-- Retorna o corpo de uma cláusula
bodyOf :: Clause -> [Term]
bodyOf (t :- ts) = ts
bodyOf (Simple t) = []
bodyOf (t :\== t') = []                   --será?

-- Verifica se dois termos unificam
match :: Term -> Term -> Bool
match (Var x) _ = True
match _ (Var x) = True
match (Atom x) (Atom y) = x == y
match (Func n1 args1) (Func n2 args2) = n1 == n2 && all (uncurry match) (zip args1 args2)           --Verifica se é a mesma função e se os argumentos podem ser unificados
match _ _ = False

-- Substitui variáveis em um termo
substitute :: (String, Term) -> Term -> Term
substitute (x, t) (Var y) = if x == y then t else Var y                                             --Se a variável for igual a x, retorna o termo t, senão retorna a variável
substitute (x, t) (Atom y) = Atom y
substitute (x, t) (Func n args) = Func n (map (substitute (x, t)) args)                             --Aplica a substituição em toda a lista de argumentos

-- Aplica a substituição em todos os termos da lista, retorna o termo substituído
substituteAll :: [(String, Term)] -> Term -> Term
substituteAll [] t = t
substituteAll ((x, t):xs) t' = substituteAll xs (substitute (x, t) t')                              --Aplica a substituição em todos os termos da lista

-- Retorna uma lista de tuplas contendo todas as substituições que unificam com um termo
unify :: Term -> Term -> Maybe [(String, Term)]
unify (Var x) t = Just [(x, t)]
unify t (Var x) = Just [(x, t)]
unify (Atom x) (Atom y) = if x == y then Just [] else Nothing
unify (Func n1 args1) (Func n2 args2) = if n1 == n2 then unifyList args1 args2 else Nothing          --Se as funções tiverem o mesmo nome, tenta unificar as listas de argumentos
unify _ _ = Nothing

-- Retorna todas as substituições que unificam com uma lista de termos
unifyList :: [Term] -> [Term] -> Maybe [(String, Term)]
unifyList [] [] = Just []
unifyList (t:ts) (t':ts') = case unify t t' of
       Nothing -> Nothing
       Just subst -> case unifyList (map (substituteAll subst) ts) (map (substituteAll subst) ts') of
              Nothing -> Nothing
              Just subst' -> Just (subst ++ subst')
unifyList _ _ = Nothing

-- Interpret a clause, returning all the substitution that unifies the head of the clause with the term
interpret :: Prolog -> Term -> Maybe [(String, Term)]
interpret prog term = case unify (headOf clause) term of                                              --Unifica a cabeça da cláusula com o termo
       Nothing -> Nothing
       Just subst -> case interpretList prog (map (substituteAll subst) (bodyOf clause)) of           --Caso unifique, aplica a substituição no corpo da cláusula?
              Nothing -> Nothing
              Just subst' -> Just (subst ++ subst')
       where clause = head (query prog term)                                                          --Busca a primeira cláusula que unifica com o termo?
             query prog term = [clause | clause <- prog, match term (headOf clause)]                  --Verifica se a cabeça da cláusula? unifica com o termo para toda cláusula do programa e retorna a lista de cláusulas que unificam com o termo - -- busca cláusulas que unificam com um termo - query myProg1 (Atom "prolog")

-- Interpreta uma lista de cláusulas
interpretList :: Prolog -> [Term] -> Maybe [(String, Term)]
interpretList _ [] = Just []
interpretList prog (t:ts) = case interpret prog t of
       Nothing -> Nothing
       Just subst -> case interpretList prog (map (substituteAll subst) ts) of
              Nothing -> Nothing
              Just subst' -> Just (subst ++ subst')

-- Aplica a substituição em todas as variáveis da lista subst
result :: Maybe [(String, Term)] -> [Term]
result Nothing = []
result (Just subst) = [substituteAll subst (Var x) | (x, _) <- subst]                                --Aplica a substituição em todas as variáveis da lista subst

-- Retorna o resultado da consulta
queryResult :: Prolog -> Term -> [Term]
queryResult prog term = case interpret prog term of 
     Nothing -> []                                        
     Just subst -> [head (result (Just subst))]

main :: IO ()
main = print (queryResult myProg1 (Func "likes" [Var "X", Atom "prolog"]))

--main :: IO ()
--main = print (queryResult myProg21 (Func "parent" [Var "X", Atom "koos"]))

--Examples

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

       --Modern Compiler Design Example page 613
myProg21 :: Prolog
myProg21 = [
       Simple (Func "parent" [Atom "arne", Atom "james"]),
       Simple (Func "parent" [Atom "arne", Atom "sachiko"]),
       Simple (Func "parent" [Atom "koos", Atom "rivka"]),
       Simple (Func "parent" [Atom "sachiko", Atom "rivka"]),
       Simple (Func "parent" [Atom "truitje", Atom "koos"])]

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