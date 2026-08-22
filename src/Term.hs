module Term
       ( Term(..)
       , Clause(..)
       , Prolog
       , Subst
       , CutState
       , PrologResult
       , nil
       , cons
       , list
       , isList
       , prettyTerm
       ) where

import Data.List (intercalate)

data Term = Var String | Atom String | Func String [Term] | Cut
          deriving (Eq, Show)

data Clause = Term :- [Term] | Simple Term
            deriving (Eq, Show)

type Prolog = [Clause]
type Subst = [(String, Term)]
type CutState = (Subst, Bool)
type PrologResult = Either String CutState

nil :: Term
nil = Atom "[]"

cons :: Term -> Term -> Term
cons h t = Func "." [h, t]

list :: [Term] -> Term
list = foldr cons nil

isList :: Term -> Bool
isList (Atom "[]") = True
isList (Func "." _) = True
isList _ = False

prettyTerm :: Term -> String
prettyTerm (Atom "[]") = "[]"
prettyTerm (Atom x)    = x
prettyTerm (Var x)     = x
prettyTerm Cut         = "!"
prettyTerm t@(Func "." _) = "[" ++ go t ++ "]"
  where
    go (Func "." [h, Atom "[]"]) = prettyTerm h
    go (Func "." [h, t'])        = prettyTerm h ++ ", " ++ go t'
    go other                     = " | " ++ prettyTerm other
prettyTerm (Func n args) = n ++ "(" ++ intercalate ", " (map prettyTerm args) ++ ")"
