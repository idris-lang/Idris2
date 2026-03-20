-- Cycle collection test for the RefC backend.
--
-- Creates reference cycles that cannot be freed by reference counting alone,
-- then relies on idris2_collectCycles() (called at program exit) to free them.
--
-- A cycle here: `ref` (IORef Tree) holds a Node whose children both point back
-- to `ref`.  After main exits the local binding, ref's refcount drops to 2
-- (held by the two Node children) rather than 0, so normal refcounting leaks it.
-- The cycle collector identifies and frees the whole cycle.

module Main

import Data.IORef

data Tree : Type where
    Leaf : Tree
    Node : IORef Tree -> IORef Tree -> Tree

-- Build a self-referential tree: ref → Node [ref, ref]
makeCycle : IO ()
makeCycle = do
    ref <- newIORef Leaf
    writeIORef ref (Node ref ref)
    -- ref now goes out of scope with refcount 2 (held by the two Node children)
    pure ()

-- Two IORefs that point to each other:
--   a → Node [b, b]
--   b → Node [a, a]
makeMutualCycle : IO ()
makeMutualCycle = do
    a <- newIORef Leaf
    b <- newIORef Leaf
    writeIORef a (Node b b)
    writeIORef b (Node a a)
    pure ()

main : IO ()
main = do
    makeCycle
    makeMutualCycle
    putStrLn "cycles created"
    putStrLn "done"
