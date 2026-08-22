module Term
       ( Term(..)
       , Clause(..)
       , Prolog
       , Subst
       , CutState
       , PrologResult
       ) where

data Term = Var String | Atom String | Func String [Term] | Cut
          deriving (Eq, Show)

data Clause = Term :- [Term] | Simple Term
            deriving (Eq, Show)

type Prolog = [Clause]
type Subst = [(String, Term)]
type CutState = (Subst, Bool)
type PrologResult = Either String CutState
