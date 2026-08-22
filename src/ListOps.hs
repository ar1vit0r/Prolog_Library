module ListOps (listProg) where

import Term
import Parse (parseProg)

listProg :: Prolog
listProg = case parseProg (unlines
  [ "member(X, [X|_])."
  , "member(X, [_|T]) :- member(X, T)."
  , "append([], L, L)."
  , "append([H|T], L, [H|R]) :- append(T, L, R)."
  , "reverse([], [])."
  , "reverse([H|T], R) :- reverse(T, RT), append(RT, [H], R)."
  , "select(X, [X|T], T)."
  , "select(X, [H|T], [H|R]) :- select(X, T, R)."
  , "perm([], [])."
  , "perm(L, [H|T]) :- select(H, L, Rest), perm(Rest, T)."
  ]) of
    Right p   -> p
    Left err  -> error (show err)
