import Control.App
import Control.App.Console

%foreign_impl Prelude.IO.prim__fork "javascript:lambda:(proc) => { throw new Error() }"

prog : (Console es) => App es ()
prog = putStrLn "hello, world"

main : IO ()
main = run prog
