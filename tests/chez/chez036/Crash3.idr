import System
partial
unreachable : a
unreachable = idris_crash "unreachable"

main : IO Int
main = do
    exitSuccess
    assert_total unreachable
