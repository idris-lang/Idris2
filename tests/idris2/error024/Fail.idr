%default total

failing "mismatch: 1 and 2"

  revAcc : List a -> List a -> List a
  revAcc [] acc = acc
  revAcc (x :: xs) acc = revAcc xs (x :: acc)

  rev : List a -> List a
  rev = revAcc []

  oops : rev [1,2] === [2,1]
  oops = Refl


failing "Failing block did not fail"

  failing ""
    -- 1. The content of this `failing' block won't fail.
    -- 2. And so the block will itself fail.
    -- 3. Which means the enclosing one will succeed in
    --    catching a "Failing block did not fail" error

    success : 'a' === 'a'
    success = Refl
