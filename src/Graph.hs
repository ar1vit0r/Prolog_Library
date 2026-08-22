module Graph (graphProg) where

import Term
import Parse (parseProg)

graphProg :: Prolog
graphProg = case parseProg (unlines
  [ "edge(a, b)."
  , "edge(b, c)."
  , "edge(c, d)."
  , "edge(d, e)."
  , "edge(b, e)."
  , "path(X, Y) :- edge(X, Y)."
  , "path(X, Y) :- edge(X, Z), path(Z, Y)."
  , "connected(X, Y) :- path(X, Y)."
  , "connected(X, Y) :- path(Y, X)."
  ]) of
    Right p  -> p
    Left err -> error (show err)
