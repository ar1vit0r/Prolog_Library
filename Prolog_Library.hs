{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

import Data.List (nub, permutations) -- nub remove elementos duplicados de uma lista, permutations retorna uma lista com todas as permutações da lista desejada.
import Data.Maybe (mapMaybe) -- mapMaybe funciona igual o map, porém, se o resultado for Nothing, ele não é adicionado na lista.

-------------------------------------- muda exemplo figura 4.
-------------------------------------- consultas nos apendices, decidir os exemplos que serão usados. tentar fazer o ultimo funciopnar. cuidar para nao ficarem cortados
-------------------------------------- na parte da interpret, cuidar o backtrack------------ para que ele não retorne o mesmo resultado, e sim o proximo.

--trabalhos futuros, problemas, caso n resolver, explicar pq n resolveu, e como resolveria, e o pq de n ter resolvido.

data Term = Var String | Atom String | Func String [Term]
       deriving (Eq,Show)
data Clause = Term :- [Term] | Simple Term
       deriving (Eq,Show)

type Prolog = [Clause]
type Subst = Maybe [(String, Term)]

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

-- Retorna as substituições realizadas e o resultado da consulta.
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

------------------------------------------------------------------------
-- Exemplo de consulta interpretando o programa e exibindo o resultado--
------------------------------------------------------------------------

-- example0 to execute all the other examples
main :: IO ()
main = do
       example
       example1
       example2
       example3
       example4
       example5
       example6
       example7

example :: IO ()
example = print (queryResult myExample (Func "mae" [Var "Q", Atom "janeti"]))     

example1 :: IO ()
example1 = print (queryResult myExample1 (Func "consulta" [Var "Q"]))

example2 :: IO ()
example2 = print (queryResult myExample2 (Func "parent" [Atom "arne", Var "X"]))

example3 :: IO ()
example3 = print (queryResult myExample3 (Func "likes" [Var "Y", Atom "prolog"]))

example4 :: IO ()
example4 = print (queryResult myExample4 (Func "professor" [Var "Y", Atom "charlie"]))

example5 :: IO ()
example5 = print (queryResult myExample5 (Func "gives" [Var "ALGUEM1", Atom "chocolate", Var "ALGUEM2"]))

example6 :: IO ()
example6 = print (queryResult myExample6 (Func "woman" [Var "X"]))

example7 :: IO ()
example7 = print (queryResult myExample7 (Func "king" [Atom "menelaus", Var "X", Var "Y"]))

--------------------------------
--Exemplo de programa Prolog----
--------------------------------

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

       --Modern Compiler Design example page 613
myExample2 :: Prolog
myExample2 = [
       Simple (Func "parent" [Atom "arne", Atom "james"]),
       Simple (Func "parent" [Atom "arne", Atom "sachiko"]),
       Simple (Func "parent" [Atom "koos", Atom "rivka"]),
       Simple (Func "parent" [Atom "sachiko", Atom "rivka"]),
       Simple (Func "parent" [Atom "truitje", Atom "koos"])]

       --Maribel example page 171
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

myExample5 :: Prolog
myExample5 = [
       Simple (Func "gives" [Atom "john", Atom "chocolate", Atom "jane"])]

myExample6 :: Prolog
myExample6 = [
       Simple (Func "woman" [Atom "mia"]),
       Simple (Func "woman" [Atom "jody"]),
       Simple (Func "woman" [Atom "yolanda"]),
       Simple (Func "loves" [Atom "vincent", Atom "mia"]),
       Simple (Func "loves" [Atom "marcellus", Atom "mia"]),
       Simple (Func "loves" [Atom "pumpkin", Atom "honey_bunny"]),
       Simple (Func "loves" [Atom "honey_bunny", Atom "pumpkin"]),
       Func "loves" [Var "X", Var "Y"] :- [Func "loves" [Var "X", Var "Y"], Func "woman" [Var "Y"]],
       Func "jealous" [Var "X", Var "Y"] :- [Func "loves" [Var "X", Var "Z"], Func "loves" [Var "Y", Var "Z"]]]

myExample7 :: Prolog
myExample7 = [
       Simple (Func "character" [Atom "priam", Atom "iliad"]),
       Simple (Func "character" [Atom "hecuba", Atom "iliad"]),
       Simple (Func "character" [Atom "achilles", Atom "iliad"]),
       Simple (Func "character" [Atom "agamemnon", Atom "iliad"]),
       Simple (Func "character" [Atom "patroclus", Atom "iliad"]),
       Simple (Func "character" [Atom "hector", Atom "iliad"]),
       Simple (Func "character" [Atom "andromache", Atom "iliad"]),
       Simple (Func "character" [Atom "rhesus", Atom "iliad"]),
       Simple (Func "character" [Atom "ulysses", Atom "iliad"]),
       Simple (Func "character" [Atom "menelaus", Atom "iliad"]),
       Simple (Func "character" [Atom "helen", Atom "iliad"]),
       Simple (Func "character" [Atom "ulysses", Atom "odyssey"]),
       Simple (Func "character" [Atom "penelope", Atom "odyssey"]),
       Simple (Func "character" [Atom "telemachus", Atom "odyssey"]),
       Simple (Func "character" [Atom "laertes", Atom "odyssey"]),
       Simple (Func "character" [Atom "nestor", Atom "odyssey"]),
       Simple (Func "character" [Atom "menelaus", Atom "odyssey"]),
       Simple (Func "character" [Atom "helen", Atom "odyssey"]),
       Simple (Func "character" [Atom "hermione", Atom "odyssey"]),
       Simple (Func "male" [Atom "priam"]),
       Simple (Func "male" [Atom "achilles"]),
       Simple (Func "male" [Atom "agamemnon"]),
       Simple (Func "male" [Atom "patroclus"]),
       Simple (Func "male" [Atom "hector"]),
       Simple (Func "male" [Atom "rhesus"]),
       Simple (Func "male" [Atom "ulysses"]),
       Simple (Func "male" [Atom "menelaus"]),
       Simple (Func "male" [Atom "telemachus"]),
       Simple (Func "male" [Atom "laertes"]),
       Simple (Func "male" [Atom "nestor"]),
       Simple (Func "female" [Atom "hecuba"]),
       Simple (Func "female" [Atom "andromache"]),
       Simple (Func "female" [Atom "helen"]),
       Simple (Func "female" [Atom "penelope"]),
       Simple (Func "father" [Atom "priam", Atom "hector"]),
       Simple (Func "father" [Atom "laertes", Atom "ulysses"]),
       Simple (Func "father" [Atom "atreus", Atom "menelaus"]),
       Simple (Func "father" [Atom "menelaus", Atom "hermione"]),
       Simple (Func "father" [Atom "ulysses", Atom "telemachus"]),
       Simple (Func "mother" [Atom "hecuba", Atom "hector"]),
       Simple (Func "mother" [Atom "penelope", Atom "telemachus"]),
       Simple (Func "mother" [Atom "helen", Atom "hermione"]),
       Simple (Func "king" [Atom "ulysses", Atom "ithaca", Atom "achaean"]),
       Simple (Func "king" [Atom "menelaus", Atom "sparta", Atom "achaean"]),
       Simple (Func "king" [Atom "nestor", Atom "pylos", Atom "achaean"]),
       Simple (Func "king" [Atom "agamemnon", Atom "argos", Atom "achaean"]),
       Simple (Func "king" [Atom "priam", Atom "troy", Atom "trojan"]),
       Simple (Func "king" [Atom "rhesus", Atom "thrace", Atom "trojan"])]