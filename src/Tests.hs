module Tests (runTests) where

import Term
import Unify
import Interpret
import Parse
import ListOps
import Graph

runTests :: IO ()
runTests = do
  putStrLn "=== Unify Tests ==="
  assert "unify atoms" (unify (Atom "a") (Atom "a")) (Just [])
  assert "unify atoms fail" (unify (Atom "a") (Atom "b")) Nothing
  assert "unify var + atom" (unify (Var "X") (Atom "a")) (Just [("X", Atom "a")])
  assert "unify func" (unify (Func "f" [Atom "a"]) (Func "f" [Atom "a"])) (Just [])
  assert "unify func args" (unify (Func "f" [Var "X"]) (Func "f" [Atom "b"])) (Just [("X", Atom "b")])
  assert "unify func mismatch" (unify (Func "f" [Atom "a"]) (Func "g" [Atom "a"])) Nothing

  putStrLn "\n=== Substitute Tests ==="
  assert "substitute var" (substituteAll [("X", Atom "a")] (Var "X")) (Atom "a")
  assert "substitute in func" (substituteAll [("X", Atom "a")] (Func "f" [Var "X", Atom "b"])) (Func "f" [Atom "a", Atom "b"])
  assert "substitute chain" (substituteAll [("X", Var "Y"), ("Y", Atom "c")] (Var "X")) (Atom "c")

  putStrLn "\n=== Query Tests ==="
  let prog = [
        Simple (Func "p" [Atom "a"]),
        Simple (Func "p" [Atom "b"]),
        Func "q" [Var "X"] :- [Func "p" [Var "X"]]
        ]
  assert "query fact" (queryResult prog (Func "p" [Var "X"])) [("X", "a")]
  assert "query rule" (queryResult prog (Func "q" [Var "X"])) [("X", "a")]

  putStrLn "\n=== Cut Tests ==="
  let cutProg = [
        Func "r" [Atom "a"] :- [Cut],
        Simple (Func "r" [Atom "b"]),
        Simple (Func "r" [Atom "c"])
        ]
  assert "cut blocks backtracking" (queryResult cutProg (Func "r" [Var "X"])) [("X", "a")]

  let noCutProg = [
        Simple (Func "s" [Atom "a"]),
        Simple (Func "s" [Atom "b"]),
        Simple (Func "s" [Atom "c"])
        ]
  assert "no cut enumerates" (queryResult noCutProg (Func "s" [Var "X"])) [("X", "a")]

  putStrLn "\n=== Family Tree Tests ==="
  let fam = familyProg
  assert "mae query" (queryResult fam (Func "mae" [Var "X", Atom "ari"])) [("X", "vitoria")]
  assert "pai query" (queryResult fam (Func "pai" [Var "X", Atom "janeti"])) [("X", "olicio")]
  assert "progenitor query" (queryResult fam (Func "progenitor" [Var "X", Atom "ari_vitor"])) [("X", "janeti")]

  putStrLn "\n=== List Operation Tests ==="
  assert "member query" (queryResult listProg (Func "member" [Var "X", list [Atom "a", Atom "b", Atom "c"]])) [("X", "a")]
  assert "append query" (queryResult listProg (Func "append" [list [Atom "a", Atom "b"], list [Atom "c", Atom "d"], Var "R"])) [("R", "[a, b, c, d]")]
  assert "reverse query" (queryResult listProg (Func "reverse" [list [Atom "a", Atom "b"], Var "R"])) [("R", "[b, a]")]
  assert "select query" (queryResult listProg (Func "select" [Atom "b", list [Atom "a", Atom "b", Atom "c"], Var "R"])) [("R", "[a, c]")]

  putStrLn "\n=== Graph Reachability Tests ==="
  assert "path from a" (queryResult graphProg (Func "path" [Atom "a", Var "X"])) [("X", "b")]
  assert "path b to e" (queryResult graphProg (Func "path" [Atom "b", Var "X"])) [("X", "c")]
  assert "connected e to a" (queryResult graphProg (Func "connected" [Atom "e", Atom "a"])) []

  putStrLn "\n=== Negation Tests ==="
  let negProg = [
        Simple (Func "flies" [Atom "superman"]),
        Func "flies" [Var "X"] :- [Func "bird" [Var "X"], Not (Func "broken" [Var "X"])]
        ]
  assert "= unification built-in" (queryResult negProg (Func "=" [Var "X", Atom "a"])) [("X", "a")]
  let negProg2 = [
        Simple (Func "p" [Atom "a"]),
        Func "q" [Var "X"] :- [Func "p" [Var "X"], Not (Func "r" [Var "X"])]
        ]
  assert "neg in body" (queryResult negProg2 (Func "q" [Var "X"])) [("X", "a")]

  putStrLn "\n=== Map Coloring Tests ==="
  let colorProg = case parseProg (unlines [
        "color(red).", "color(green).", "color(blue).",
        "coloring(A, B, C, D) :-",
        "  color(A), color(B), color(C), color(D),",
        "  \\+(A = B), \\+(B = C), \\+(C = D), \\+(A = C)."
        ]) of Right p -> p; Left e -> error (show e)
  assert "map coloring" (queryResult colorProg (Func "coloring" [Var "A", Var "B", Var "C", Var "D"])) [("A", "red"), ("B", "green"), ("C", "blue"), ("D", "red")]

  putStrLn "\n=== Arithmetic Tests ==="
  let arithProg = case parseProg (unlines [
        "fib(0, 0).",
        "fib(1, 1).",
        "fib(N, F) :- N > 1, N1 is N - 1, N2 is N - 2, fib(N1, F1), fib(N2, F2), F is F1 + F2.",
        "fact(0, 1).",
        "fact(N, F) :- N > 0, N1 is N - 1, fact(N1, F1), F is F1 * N.",
        "list_len([], 0).",
        "list_len([_|T], N) :- list_len(T, N1), N is N1 + 1.",
        "sum_list([], 0).",
        "sum_list([H|T], S) :- sum_list(T, S1), S is S1 + H.",
        "even(N) :- N mod 2 =:= 0.",
        "max(A, B, A) :- A >= B.",
        "max(A, B, B) :- A < B."
        ]) of Right p -> p; Left e -> error (show e)
  assert "fib 0" (queryResult arithProg (Func "fib" [Atom "0", Var "F"])) [("F", "0")]
  assert "fib 1" (queryResult arithProg (Func "fib" [Atom "1", Var "F"])) [("F", "1")]
  assert "fib 6" (queryResult arithProg (Func "fib" [Atom "6", Var "F"])) [("F", "8")]
  assert "fact 5" (queryResult arithProg (Func "fact" [Atom "5", Var "F"])) [("F", "120")]
  assert "list_len" (queryResult arithProg (Func "list_len" [list [Atom "a", Atom "b", Atom "c"], Var "N"])) [("N", "3")]
  assert "sum_list" (queryResult arithProg (Func "sum_list" [list [Atom "1", Atom "2", Atom "3"], Var "S"])) [("S", "6")]
  assert "max query" (queryResult arithProg (Func "max" [Atom "3", Atom "5", Var "M"])) [("M", "5")]

  putStrLn "\n=== All tests passed ==="

familyProg :: Prolog
familyProg = [
  Simple (Func "progenitor" [Atom "joao", Atom "ari"]),
  Simple (Func "progenitor" [Atom "vitoria", Atom "ari"]),
  Simple (Func "progenitor" [Atom "paulina", Atom "janeti"]),
  Simple (Func "progenitor" [Atom "olicio", Atom "janeti"]),
  Simple (Func "progenitor" [Atom "janeti", Atom "ari_vitor"]),
  Simple (Func "sexo" [Atom "ari", Atom "masculino"]),
  Simple (Func "sexo" [Atom "vitoria", Atom "feminino"]),
  Simple (Func "sexo" [Atom "olicio", Atom "masculino"]),
  Simple (Func "sexo" [Atom "janeti", Atom "feminino"]),
  Func "mae" [Var "X", Var "Y"] :- [
    Func "progenitor" [Var "X", Var "Y"],
    Func "sexo" [Var "X", Atom "feminino"]
  ],
  Func "pai" [Var "X", Var "Y"] :- [
    Func "progenitor" [Var "X", Var "Y"],
    Func "sexo" [Var "X", Atom "masculino"]
  ]
  ]

assert :: (Eq a, Show a) => String -> a -> a -> IO ()
assert name got expected
  | got == expected = putStrLn $ "  OK: " ++ name
  | otherwise = error $ "  FAIL: " ++ name ++ "\n    got:      " ++ show got ++ "\n    expected: " ++ show expected
