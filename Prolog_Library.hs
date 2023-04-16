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

-- Substitui uma variável por um termo em um outro termo passado como argumento e retorna o termo substituído.
substitute :: (String, Term) -> Term -> Term
substitute (x, t) (Atom y) = Atom y
substitute (x, t) (Var y) = if x == y then t else Var y                                             --Se a variável for igual a x, retorna o termo t, senão retorna a variável.
substitute (x, t) (Var a :\== Var b) = if x == a then Var b :\== Var b else Var a :\== Var b        --Substitui a variável em uma expressão de desigualdade.
substitute (x, t) (Func n args) = Func n (map (substitute (x, t)) args)                             --Aplica a substituição em toda a lista de argumentos.

substituteAll :: [(String, Term)] -> Term -> Term
substituteAll [] t = t
substituteAll ((x, t):xs) t' = substituteAll xs (substitute (x, t) t')                              --Aplica a substituição em todos os termos da lista.

generateNewVarName :: String -> [String] -> String
generateNewVarName x usedVars = if x `elem` usedVars then generateNewVarName (x ++ "'") usedVars else x

-- Conversão Alfa - Gera sempre uma nova variável para substituir a variável da consulta. Ex: X = Y, gera uma nova variável Z e substitui todas as ocorrências de X por Z.
alphaConversion :: Term -> [String] -> Term
alphaConversion (Atom x) usedVars = Atom x
alphaConversion (Var x) usedVars = Var (generateNewVarName x usedVars)
alphaConversion (Func n args) usedVars =
       let args' = map (`alphaConversion` usedVars) args
       in Func n args'
alphaConversion t _ = t

-- Retorna todas as substituições que unificam com um termo.
unify :: Term -> Term -> [String] -> Subst
unify (Atom x) (Atom y) vars = if x == y then Just [] else Nothing                                        --Se forem átomos, verifica se são iguais e retorna a substituição vazia.
unify (Var x) (Var y) vars = Just [(x, Var y)]                                                            --Se forem variáveis, retorna a substituição, pois variaveis sempre podem ser unificadas.
unify t (Var x) vars = Just [(x, t)]                                                                      --Se o termo for uma variável, retorna a substituição.
unify (Var x) t vars = Just [(x, t)]                                                                      --Se o termo for uma variável, retorna a substituição.
unify (Var t :\== Var t') _  vars= if t == t' then Just [] else Nothing
unify (Func n1 args1) (Func n2 args2) vars = if n1 == n2 && length args1 == length args2 then unifyList args1 args2 vars else Nothing--Se as funções tiverem o mesmo nomee o mesmo número de argumentos, tenta unificar as listas de argumentos.
unify _ _ _= Nothing

-- Unifica dois termos aplicando a conversão alfa
unifyWithAlphaConversion :: Term -> Term -> [String] -> Subst
unifyWithAlphaConversion t1 t2 vars =
       let t1' = alphaConversion t1 vars
           t2' = alphaConversion t2 vars
       in unify t1' t2' vars

unifyList :: [Term] -> [Term] -> [String] -> Subst
unifyList [] [] _ = Just []
unifyList (t:ts) (t':ts') vars = case unifyWithAlphaConversion t t' vars of
       Nothing -> Nothing
       Just subst -> case unifyList (map (substituteAll subst) ts) (map (substituteAll subst) ts') vars of
              Nothing -> Nothing
              Just subst' -> Just (subst ++ subst')
unifyList _ _ _ = Nothing

-- Interpreta o programa, percorre cada cláusula e gera uma lista de substituições a serem realizadas.
interpret :: Prolog -> Term -> [String] -> Subst
interpret prog term vars = case query prog term of
       [] -> Nothing
       (clause:_) -> case unifyWithAlphaConversion (headOf clause) term vars of
              Nothing -> Nothing
              Just subst -> case interpretList prog (map (substituteAll subst) (bodyOf clause)) vars of
                     Nothing -> Nothing
                     Just subst' -> Just (subst ++ subst')
       where query prog term = [clause | clause <- prog, match term (headOf clause)]

-- Interpreta o programa aplicando a conversão alfa em cada cláusula e no termo da consulta.
interpretWithAlphaConversion :: Prolog -> Term -> [String] -> Subst
interpretWithAlphaConversion prog term vars =
       let prog' = applyAlphaConversion prog vars
           term' = alphaConversion term vars
       in interpret prog' term' vars
       where
              applyAlphaConversion prog vars = map (`applyAlphaConversionClause` vars) prog
                     where
                            applyAlphaConversionTerm t vars = alphaConversion t vars
                            applyAlphaConversionClause (Simple t) vars = Simple (applyAlphaConversionTerm t vars)
                            applyAlphaConversionClause (head :- body) vars = applyAlphaConversionTerm head vars :- map (`applyAlphaConversionTerm` vars) body

interpretList :: Prolog -> [Term] -> [String] -> Subst
interpretList _ [] _ = Just []
interpretList prog (t:ts) vars= case interpretWithAlphaConversion prog t vars of
       Nothing -> Nothing
       Just subst -> case interpretList prog (map (substituteAll subst) ts) vars of
              Nothing -> Nothing
              Just subst' -> Just (subst ++ subst')

-- Aplica a substituição em todas as variáveis da lista subst e retorna o resultado.
result :: Subst -> [Term]
result Nothing = []
result (Just subst) = [substituteAll subst (Var x) | (x, _) <- subst]                                --Aplica a substituição em todas as variáveis da lista subst.

-- Retorna o resultado da consulta, caso não encontrar, tenta novamente para todas permutas da lista.
queryResult :: Prolog -> Term -> [Term]
queryResult prog term = case interpretWithAlphaConversion prog term (usedVars prog) of
       Nothing -> []
       Just subst -> [head (result (Just subst))]
       where
              usedVars prog = nub (concatMap usedVarsClause prog)
                     where
                            usedVarsClause (t :- ts) = usedVarsTerm t ++ concatMap usedVarsTerm ts
                            usedVarsClause (Simple t) = usedVarsTerm t
                            usedVarsTerm (Atom x) = []
                            usedVarsTerm (Var x) = [x]
                            usedVarsTerm (Var a :\== Var b) = [a, b]
                            usedVarsTerm (Func n args) = concatMap usedVarsTerm args

main1 :: IO ()
main1 = print (queryResult myExample1 (Func "parent" [Var "X", Atom "koos"]))

main2 :: IO ()
main2 = print (queryResult myExample2 (Func "likes" [Atom "prolog", Var "X"]))

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