{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

import Data.List (nub) -- nub remove elementos duplicados de uma lista.

-- https://downloads.haskell.org/~ghc/7.2.1/docs/html/users_guide/pragmas.html - 7.13.5.1. INLINE pragma - GHC User's Guide

data Term = Var String | Atom String | Func String [Term] | Term :\== Term
       deriving (Eq,Show)
data Clause = Term :- [Term] | Simple Term
       deriving (Eq,Show)

type Prolog = [Clause]
type Subst = Maybe [(String, Term)]

-- Retorna o resultado da consulta, caso não encontrar, tenta novamente para todas permutas da lista.
queryResult :: Prolog -> Term -> [Term]
queryResult prog term = case interpretWithAlphaConversion prog term (usedVars prog) of
       Nothing -> case term of
              Func n xs -> queryResultAux prog (Func n (reverse xs))                                                --Inverte a lista de argumentos do termo, necessita ser uma função auxiliar para não entrar em loop infinito.
              _ -> []
       Just solution -> [head (result (Just solution))]
       where
              result Nothing = []
              result (Just subst) = [substituteAll subst (Var x) | (x, _) <- subst]                                 --Desencapsula o Maybe e retorna o resultado.
              queryResultAux prog term = case interpretWithAlphaConversion prog term (usedVars prog) of
                     Just subst -> [head (result (Just subst))]
                     Nothing -> []
              usedVars prog = nub (concatMap usedVarsClause prog) ++ nub (usedVarsTerm term)                        --Retorna uma lista com todas as variáveis usadas no programa e no termo da consulta.
                     where
                            usedVarsClause (t :- ts) = usedVarsTerm t ++ concatMap usedVarsTerm ts
                            usedVarsClause (Simple t) = usedVarsTerm t
                            usedVarsTerm (Atom x) = []
                            usedVarsTerm (Var x) = [x]
                            usedVarsTerm (Var a :\== Var b) = [a, b]
                            usedVarsTerm (Func n args) = concatMap usedVarsTerm args

-- Invoca a função interpret com a conversão alfa aplicada em cada cláusula do programa e no termo da consulta.
interpretWithAlphaConversion :: Prolog -> Term -> [String] -> Subst
interpretWithAlphaConversion prog term usedVars =
       let prog' = applyAlphaConversion prog usedVars
           term' = alphaConversion term usedVars
       in interpret prog' term' usedVars
       where
              alphaConversion (Atom x) usedVars = Atom x                                                                        -- alphaConversion (Func "consulta" [Atom "ariel", Var "P"]) ["X", "P"]
              alphaConversion (Var x) usedVars = Var (generateNewVarName x usedVars)
                     where
                            generateNewVarName var usedVars = if var `elem` usedVars then generateNewVarName (var ++ "'") usedVars else var--Gera uma nova variável para substituir a variável da consulta. Ex: X = Y, gera uma nova variável Z e substitui todas as ocorrências de X por Z.
              alphaConversion (Func n args) usedVars = let args' = map (`alphaConversion` usedVars) args in Func n args'--Aplica a conversão alfa em cada argumento da função. Retorna a função com os argumentos convertidos.
              alphaConversion t _ = t
              applyAlphaConversion prog usedVars = map (`applyAlphaConversionClause` usedVars) prog
                     where
                            applyAlphaConversionTerm t usedVars = alphaConversion t usedVars
                            applyAlphaConversionClause (Simple t) usedVars = Simple (applyAlphaConversionTerm t usedVars)
                            applyAlphaConversionClause (head :- body) usedVars = applyAlphaConversionTerm head usedVars :- map (`applyAlphaConversionTerm` usedVars) body

-- Percorre cada cláusula e aplica a unificação com o termo da consulta.
interpret :: Prolog -> Term -> [String] -> Subst
interpret prog term usedVars = case query prog term of
       [] -> Nothing
       (clause:_) -> case unify (headOf clause) term of
              Nothing -> Nothing
              Just subst -> case interpretList prog (map (substituteAll subst) (bodyOf clause)) usedVars of
                     Nothing -> Nothing
                     Just subst' -> Just (subst ++ subst')
       where
              interpretList _ [] _ = Just []
              interpretList prog (t:ts) usedVars = case interpretWithAlphaConversion prog t usedVars of--Recursão que percorre cada termo da lista de termos da cláusula e aplica a unificação com o termo da consulta
                     Nothing -> Nothing
                     Just subst -> case interpretList prog (map (substituteAll subst) ts) usedVars of
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
                            match (Var t :\== Var t') _ = t /= t'
                            match (Func n1 args1) (Func n2 args2) = n1 == n2 && length args1 == length args2 && all (uncurry match) (zip args1 args2)--Verifica se é a mesma função e se os argumentos podem ser unificados.                      
                            match _ _ = False

-- Recebe uma lista de substituições a serem realizadas e o termo onde as substituições serão realizadas.
substituteAll :: [(String, Term)] -> Term -> Term
substituteAll [] t = t
substituteAll ((x, t):xs) t' = substituteAll xs (substitute (x, t) t')                                            --Realiza uma lista de substituições em um termo.
       where
              substitute (x, t) (Atom y) = Atom y
              substitute (x, t) (Var y) = if x == y then t else Var y                                             --Se a variável for igual a x, retorna o termo t, senão retorna a variável.
              substitute (x, t) (Var a :\== b)
                     | a == x && t /= b = t :\== b
                     | otherwise = Var a :\== b
              substitute (x, t) (a :\== Var b)
                     | b == x && t /= a = a :\== t
                     | otherwise = a :\== Var b
              substitute (x, t) (Func n args) = Func n (map (substitute (x, t)) args)                             --Aplica a substituição em cada argumento da função.

-- Retorna uma lista de substituições a serem realizadas para que dois termos que deram match sejam unificados.
unify :: Term -> Term -> Subst
unify (Atom x) (Atom y) = if x == y then Just [] else Nothing
unify (Var x) (Var a :\== Var b) = if Var x == Var a && Var x /= Var b then Just [] else Nothing
unify (Atom x) (Var a :\== Var b) = Just [(a, Atom x)]
unify (Atom x) (Var a :\== b) = if Atom x /= b then Just [(a, Atom x)] else Nothing
unify (Func n args) (Atom a :\== Atom b) = if a == b then Nothing else Just [(a, Func n args)]                    -- quase, é algo próximo disto.
unify (Func n args) (Var a :\== Var b) = Just [(a, Func n args)]
unify t (Var x)  = Just [(x, t)]
unify (Var x) t = unify t (Var x) 
unify (Func n1 args1) (Func n2 args2) = if n1 == n2 && length args1 == length args2 then unifyList args1 args2 else Nothing
       where
              unifyList [] [] = Just []
              unifyList (t:ts) (t':ts') = case unify t t' of
                     Nothing -> Nothing
                     Just subst -> case unifyList (map (substituteAll subst) ts) (map (substituteAll subst) ts') of
                            Nothing -> Nothing
                            Just subst' -> Just (subst ++ subst')
              unifyList _ _  = Nothing

--------------------------------------------------------------------------
-- Exemplos de consultas interpretando o programa e exibindo o resultado--
--------------------------------------------------------------------------

main :: IO ()
main = print (queryResult myExample (Func "consulta" [Var "Q"]))

main1 :: IO ()
main1 = print (queryResult myExample1 (Func "parent" [Var "X", Atom "james"]))

main2 :: IO ()
main2 = print (queryResult myExample2 (Func "likes" [Atom "prolog", Var "Q"]))             -- aqui não funciona alpha conversion pq??

main3 :: IO ()
main3 = print (queryResult myExample3 (Func "irmao" [Var "Q", Atom "ariel"]))              -- aqui funciona alpha conversion      

--------------------------------
--Exemplos de programas Prolog--
--------------------------------

myExample :: Prolog
myExample = [
       Simple (Func "irmao" [Atom "andre", Atom "joao"]),
       Func "consulta" [Var "X"] :- [Func "irmao" [Atom "andre", Var "X"]]]

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

       --Genealogic Tree Example
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