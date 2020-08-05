module Main

-- When generating javasript from idris, it is possible that the same name may appear in
-- different clauses when translating cases from Idris. To avoid a javascript syntax error
-- from occuring due to duplicate declations, each case clause is wrapped in brackets
-- to create unique block scopes.

-- https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Statements/switch

-- Without wrapping in a block, the test error may look like the following:
-- syntax001/build/exec/_tmp_node.js:39
-- const x = ({h:1});
--         ^
-- SyntaxError: Identifier 'x' has already been declared

test : Bool -> Int
test x @ True =
  case x of
    _ => 0
test x @ False =
  case x of
    _ => 1

main : IO ()
main = do
  printLn $ test True
  printLn $ test False
