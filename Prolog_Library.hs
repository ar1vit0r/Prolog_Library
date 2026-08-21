module Main where

import Examples
import Tests

main :: IO ()
main = do
  putStrLn "=== Prolog_Library ==="
  putStrLn ""

  putStrLn "Example 1: mae(Y, ari_vitor)"
  print ex1

  putStrLn "Example 2: pai(Q, janeti)"
  print ex2

  putStrLn "Example 3: mae(X, ari)"
  print ex3

  putStrLn "Example 4: progenitor(X, ari_vitor)"
  print ex4

  putStrLn "Example 5: progenitor(ari, Y)"
  print ex5

  putStrLn "Example 6: progenitor(X, Y)"
  print ex6

  putStrLn ""
  runTests
