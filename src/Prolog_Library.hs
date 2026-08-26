-- | Entry point: runs example queries and the test suite.
module Main where

import Term
import Interpret
import Examples
import ListOps
import Graph
import Tests

main :: IO ()
main = do
  putStrLn "=== Prolog_Library ==="
  putStrLn ""

  putStrLn "--- Family Tree ---"
  print ex1
  print ex2
  print ex3

  putStrLn ""
  putStrLn "--- List Operations ---"
  print (queryResult listProg (Func "member" [Var "X", list [Atom "a", Atom "b", Atom "c"]]))
  print (queryResult listProg (Func "append" [list [Atom "a", Atom "b"], list [Atom "c", Atom "d"], Var "R"]))
  print (queryResult listProg (Func "reverse" [list [Atom "a", Atom "b", Atom "c"], Var "R"]))

  putStrLn ""
  putStrLn "--- Graph Reachability ---"
  print (queryResult graphProg (Func "path" [Atom "a", Var "X"]))
  print (queryResult graphProg (Func "path" [Var "X", Atom "e"]))

  putStrLn ""
  runTests
