module Examples
       ( myExample
       , ex1
       , ex2
       , ex3
       , ex4
       , ex5
       , ex6
       ) where

import Term
import Interpret

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
  Func "mae" [Var "X", Var "Y"] :- [
    Func "progenitor" [Var "X", Var "Y"],
    Func "sexo" [Var "X", Atom "feminino"]
  ],
  Func "pai" [Var "X", Var "Y"] :- [
    Func "progenitor" [Var "X", Var "Y"],
    Func "sexo" [Var "X", Atom "masculino"]
  ]
  ]

ex1 :: [(String, String)]
ex1 = queryResult myExample (Func "mae" [Var "Y", Atom "ari_vitor"])

ex2 :: [(String, String)]
ex2 = queryResult myExample (Func "pai" [Var "Q", Atom "janeti"])

ex3 :: [(String, String)]
ex3 = queryResult myExample (Func "mae" [Var "X", Atom "ari"])

ex4 :: [(String, String)]
ex4 = queryResult myExample (Func "progenitor" [Var "X", Atom "ari_vitor"])

ex5 :: [(String, String)]
ex5 = queryResult myExample (Func "progenitor" [Atom "ari", Var "Y"])

ex6 :: [(String, String)]
ex6 = queryResult myExample (Func "progenitor" [Var "X", Var "Y"])
