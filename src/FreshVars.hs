-- | Fresh variable generation and alpha-conversion for clauses.
-- Uses a global IORef counter (via unsafePerformIO) which is safe
-- for this single-threaded interpreter.
module FreshVars
       ( freshenClauseIO
       , renameIO
       ) where

import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad (foldM)
import Term
import Unify (varsInTerm)

{-# NOINLINE counter #-}
counter :: IORef Int
counter = unsafePerformIO (newIORef 0)

freshVarIO :: IO String
freshVarIO = do
  n <- readIORef counter
  writeIORef counter (n + 1)
  return ("_V" ++ show n)

collectClauseVars :: Clause -> [String]
collectClauseVars (Simple t) = varsInTerm t
collectClauseVars (t :- body) = varsInTerm t ++ concatMap varsInTerm body

unique :: Eq a => [a] -> [a]
unique [] = []
unique (x:xs) = x : unique (filter (/= x) xs)

freshenClauseIO :: Clause -> IO Clause
freshenClauseIO c = do
  let allVars = unique (collectClauseVars c)
  mapping <- mapM (\v -> do { v' <- freshVarIO; return (v, v') }) allVars
  return (applyClauseMapping mapping c)

applyClauseMapping :: [(String, String)] -> Clause -> Clause
applyClauseMapping m (Simple t) = Simple (applyTermMapping m t)
applyClauseMapping m (t :- body) =
  applyTermMapping m t :- map (applyTermMapping m) body

applyTermMapping :: [(String, String)] -> Term -> Term
applyTermMapping _ (Atom x) = Atom x
applyTermMapping _ Cut = Cut
applyTermMapping m (Var x) = case lookup x m of
  Just x' -> Var x'
  Nothing -> Var x
applyTermMapping m (Func n args) = Func n (map (applyTermMapping m) args)
applyTermMapping m (Not t) = Not (applyTermMapping m t)

renameIO :: Term -> IO (Term, [(String, String)])
renameIO t = do
  (t', mapping) <- renameIOAcc t []
  return (t', mapping)

renameIOAcc :: Term -> [(String, String)] -> IO (Term, [(String, String)])
renameIOAcc (Atom x) acc = return (Atom x, acc)
renameIOAcc Cut acc = return (Cut, acc)
renameIOAcc (Var x) acc = case lookup x acc of
  Just freshName -> return (Var freshName, acc)
  Nothing -> do
    freshName <- freshVarIO
    return (Var freshName, acc ++ [(x, freshName)])
renameIOAcc (Func n args) acc = do
  (args', acc') <- foldM go ([], acc) args
  return (Func n (reverse args'), acc')
  where
    go (as, a) arg = do
      (arg', a') <- renameIOAcc arg a
      return (arg':as, a')
renameIOAcc (Not t) acc = do
  (t', acc') <- renameIOAcc t acc
  return (Not t', acc')
