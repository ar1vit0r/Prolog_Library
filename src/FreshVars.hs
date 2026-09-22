-- | Fresh variable generation and alpha-conversion for clauses.
-- Uses a global IORef counter (via unsafePerformIO) which is safe
-- for this single-threaded interpreter.
module FreshVars
       ( freshenClauseIO
       , renameIO
       , renameIOAcc
       , renameManyIOAcc
       ) where

import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad (foldM)
import Term

{-# NOINLINE counter #-}
counter :: IORef Int
counter = unsafePerformIO (newIORef 0)

freshVarIO :: IO String
freshVarIO = do
  n <- readIORef counter
  writeIORef counter (n + 1)
  return ("_V" ++ show n)

-- | Alpha-convert every variable in a clause (head and body) to a fresh
-- name, sharing one mapping across the whole clause so repeated variables
-- stay consistent.
freshenClauseIO :: Clause -> IO Clause
freshenClauseIO (Simple t) = do
  (t', _) <- renameIO t
  return (Simple t')
freshenClauseIO (t :- body) = do
  (t', acc) <- renameIOAcc t []
  (body', _) <- renameManyIOAcc acc body
  return (t' :- body')

-- | Alpha-convert a single term to fresh variable names.
renameIO :: Term -> IO (Term, [(String, String)])
renameIO t = renameIOAcc t []

-- | Alpha-convert a term, extending an existing variable mapping so that
-- a variable already seen (e.g. shared between a clause's head and body,
-- or across several terms) gets the same fresh name every time.
renameIOAcc :: Term -> [(String, String)] -> IO (Term, [(String, String)])
renameIOAcc (Atom x) acc = return (Atom x, acc)
renameIOAcc Cut acc = return (Cut, acc)
renameIOAcc (Var x) acc = case lookup x acc of
  Just freshName -> return (Var freshName, acc)
  Nothing -> do
    freshName <- freshVarIO
    return (Var freshName, acc ++ [(x, freshName)])
renameIOAcc (Func n args) acc = do
  (args', acc') <- renameManyIOAcc acc args
  return (Func n args', acc')
renameIOAcc (Not t) acc = do
  (t', acc') <- renameIOAcc t acc
  return (Not t', acc')

-- | Alpha-convert a list of terms left-to-right, threading the mapping
-- through so variables shared across the terms stay consistent.
renameManyIOAcc :: [(String, String)] -> [Term] -> IO ([Term], [(String, String)])
renameManyIOAcc acc0 ts = do
  (ts', acc') <- foldM go ([], acc0) ts
  return (reverse ts', acc')
  where
    go (done, acc) t = do
      (t', acc') <- renameIOAcc t acc
      return (t':done, acc')
