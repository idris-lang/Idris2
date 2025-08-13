%default total

failing "Mismatch between: 1 and 2."

  revAcc : List a -> List a -> List a
  revAcc [] acc = acc
  revAcc (x :: xs) acc = revAcc xs (x :: acc)

  -- this implementation is buggy:
  -- we defined the identity rather than reverse
  rev : List a -> List a
  rev = revAcc []

  -- and so this test will fail
  oops : rev [1,2] === [2,1]
  oops = Refl

failing "Undefined name rev."

  -- Definitions in a `failing' block are not in scope in the rest of the file
  -- and so this will fail with a scope error on `rev' defined above.
  oops : rev [1,2] === [1,2]
  oops = Refl

failing "Failing block did not fail."

  failing
    -- 1. The content of this `failing' block won't fail.
    -- 2. And so the block will itself fail.
    -- 3. Which means the enclosing one will succeed in
    --    catching a "Failing block did not fail" error

    success : 'a' === 'a'
    success = Refl

failing "Last statement in do block must be an expression"
  invalidDoBlock : Nat -> Nat -> Maybe Nat
  invalidDoBlock = do
    x <- m <$ guard (m <= n)

failing #"Expected "Invalid" but got: Unknown operator '&&&'"#

  failing "Invalid"
    test : Nat
    test = 3 &&& 4
