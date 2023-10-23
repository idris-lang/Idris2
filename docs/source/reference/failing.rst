Failing blocks
==============

.. role:: idris(code)
    :language: idris

Failing blocks let users check that some code parses but is rejected during
elaboration. Their simplest form is using the keyword ``failing`` followed by
some indented Idris code:

.. code-block:: idris

    failing
      trueNotFalse : True === False
      trueNotFalse = Refl

Putting the code above in a file and asking Idris to check it will not produce
an error message since the code in the ``failing`` block is rejected, i.e.
fails.

The ``failing`` keyword optionally takes a string argument. If present, the
string attached to the failing block is checked against the error message raised
to check that it appears in the error. This lets the user document the kind of
error expected in the block, while at the same time checking that the error
message is indeed what we expected. For example, in the following example, we
make sure that Idris rejects a proof that the character ``'a'`` is equal to
``'b'`` by throwing an error when unifying them:

.. code-block:: idris

    failing "When unifying"
      noteq : 'a' === 'b'
      noteq = Refl

Failing blocks can be helpful when demonstrating false paths or starts in a
program or example. Valid code is accepted in failing blocks, so intermediary
helper functions can be used as long as at least one statement in the block
fails (it does not have to be the first or last statement!):

.. code-block:: idris

    failing "Mismatch between: Integer and Double"
      record Point where
        constructor MkPoint
        x : Integer
        y : Integer

      Origin : Point
      Origin = MkPoint 0 0

      dist : Point -> Point -> Integer
      dist p1 p2 = sqrt $ (pow (p2.x - p1.x) 2) + (pow (p2.y - p1.y) 2)

Invalid failing blocks
----------------------

Should the failing block not fail, i.e. the code inside is accepted during
elaboration, the compiler will report an error:

.. code-block:: idris

    failing
      validRefl : 1 === 1
      validRefl = Refl

Checking the above gives:

::

    Error: Failing block did not fail.

Similarly, if an expected error (sub)string is given but the error output does
not match, we get:

::

    Error: Failing block failed with the wrong error.

Followed by the given expected error string and the actual error output,
allowing us to compare and contrast.

One block per falsehood
-----------------------

**Take care to use separate ``failing`` blocks per thing to check.** Using a
single block can lead to unexpected results. The following example passes, since
the second statement fails:

.. code-block:: idris

    failing
      stmt1 : True === True
      stmt1 = Refl

      -- at least one failing statement, so the block is accepted
      stmt2 : 'a' === 'b'
      stmt2 = Refl

      stmt3 : 1 === 1
      stmt3 = Refl

Instead, separate the statements out into separate failing blocks:

.. code-block:: idris

    failing
      stmt1 : True === True
      stmt1 = Refl

    failing
      stmt2 : 'a' === 'b'
      stmt2 = Refl

    failing
      stmt3 : 1 === 1
      stmt3 = Refl

This causes two ``Error: Failing block did not fail`` messages to be emitted, as
one would expect.

