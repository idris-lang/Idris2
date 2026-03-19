-- Test that idris2_crash writes "ERROR: msg" to stderr and exits 1.
partial
main : IO ()
main = idris_crash "test crash message"
