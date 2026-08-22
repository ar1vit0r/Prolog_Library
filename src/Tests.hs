module Tests (runTests) where

import Term
import Unify
import Interpret

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
