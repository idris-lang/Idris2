.. _sect-interactive:

*******************
Interactive Editing
*******************

By now, we have seen several examples of how Idris’ dependent type
system can give extra confidence in a function’s correctness by giving
a more precise description of its intended behaviour in its *type*. We
have also seen an example of how the type system can help with embedded DSL
development by allowing a programmer to describe the type system of an
object language. However, precise types give us more than verification
of programs — we can also use the type system to help write programs which
are *correct by construction*, interactively.

The Idris REPL provides several commands for inspecting and
modifying parts of programs, based on their types, such as case
splitting on a pattern variable, inspecting the type of a
hole, and even a basic proof search mechanism. In this
section, we explain how these features can be exploited by a text
editor, and specifically how to do so in `Vim
<https://github.com/edwinb/idris2-vim>`_. An interactive mode
for `Emacs <https://github.com/idris-hackers/idris-mode>`_ is also
available, updated for Idris 2 compatibility as of 23 February 2021.

Editing at the REPL
===================

.. note::
  The Idris2 repl does not support readline in the interest of
  keeping dependencies minimal. Unfortunately this precludes some
  niceties such as line editing, persistent history and completion.
  A useful work around is to install `rlwrap <https://linux.die.net/man/1/rlwrap>`_,
  this utility provides all the aforementioned features simply by
  invoking the Idris2 repl as an argument to the utility ``rlwrap idris2``

The REPL provides a number of commands, which we will describe
shortly, which generate new program fragments based on the currently
loaded module. These take the general form:

::

    :command [line number] [name]

That is, each command acts on a specific source line, at a specific
name, and outputs a new program fragment. Each command has an
alternative form, which *updates* the source file in-place:

::

    :command! [line number] [name]

It is also possible to invoke Idris in a mode which runs a REPL command,
displays the result, then exits, using ``idris2 --client``. For example:

::

    $ idris2 --client ':t plus'
    Prelude.plus : Nat -> Nat -> Nat
    $ idris2 --client '2+2'
    4

A text editor can take advantage of this, along with the editing
commands, in order to provide interactive editing support.

Editing Commands
================

:addclause
----------

The ``:addclause n f`` command, abbreviated ``:ac n f``, creates a
template definition for the function named ``f`` declared on line
``n``. For example, if the code beginning on line 94 contains:

.. code-block:: idris

    vzipWith : (a -> b -> c) ->
               Vect n a -> Vect n b -> Vect n c

then ``:ac 94 vzipWith`` will give:

.. code-block:: idris

    vzipWith f xs ys = ?vzipWith_rhs

The names are chosen according to hints which may be given by a
programmer, and then made unique by the machine by adding a digit if
necessary. Hints can be given as follows:

.. code-block:: idris

    %name Vect xs, ys, zs, ws

This declares that any names generated for types in the ``Vect`` family
should be chosen in the order ``xs``, ``ys``, ``zs``, ``ws``.

:casesplit
----------

The ``:casesplit n c x`` command, abbreviated ``:cs n c x``, splits the
pattern variable ``x`` on line ``n`` at column ``c`` into the various
pattern forms it may take, removing any cases which are impossible due
to unification errors. For example, if the code beginning on line 94 is:

.. code-block:: idris

    vzipWith : (a -> b -> c) ->
               Vect n a -> Vect n b -> Vect n c
    vzipWith f xs ys = ?vzipWith_rhs

then ``:cs 96 12 xs`` will give:

.. code-block:: idris

    vzipWith f [] ys = ?vzipWith_rhs_1
    vzipWith f (x :: xs) ys = ?vzipWith_rhs_2

That is, the pattern variable ``xs`` has been split into the two
possible cases ``[]`` and ``x :: xs``. Again, the names are chosen
according to the same heuristic. If we update the file (using
``:cs!``) then case split on ``ys`` on the same line, we get:

.. code-block:: idris

    vzipWith f [] [] = ?vzipWith_rhs_3

That is, the pattern variable ``ys`` has been split into one case
``[]``, Idris having noticed that the other possible case ``y ::
ys`` would lead to a unification error.

:addmissing
-----------

The ``:addmissing n f`` command, abbreviated ``:am n f``, adds the
clauses which are required to make the function ``f`` on line ``n``
cover all inputs. For example, if the code beginning on line 94 is:

.. code-block:: idris

    vzipWith : (a -> b -> c) ->
               Vect n a -> Vect n b -> Vect n c
    vzipWith f [] [] = ?vzipWith_rhs_1

then ``:am 96 vzipWith`` gives:

.. code-block:: idris

    vzipWith f (x :: xs) (y :: ys) = ?vzipWith_rhs_2

That is, it notices that there are no cases for empty vectors,
generates the required clauses, and eliminates the clauses which would
lead to unification errors.

:proofsearch
------------

The ``:proofsearch n f`` command, abbreviated ``:ps n f``, attempts to
find a value for the hole ``f`` on line ``n`` by proof search,
trying values of local variables, recursive calls and constructors of
the required family. Optionally, it can take a list of *hints*, which
are functions it can try applying to solve the hole. For
example, if the code beginning on line 94 is:

.. code-block:: idris

    vzipWith : (a -> b -> c) ->
               Vect n a -> Vect n b -> Vect n c
    vzipWith f [] [] = ?vzipWith_rhs_1
    vzipWith f (x :: xs) (y :: ys) = ?vzipWith_rhs_2

then ``:ps 96 vzipWith_rhs_1`` will give

.. code-block:: idris

   []

This works because it is searching for a ``Vect`` of length 0, of
which the empty vector is the only possibility. Similarly, and perhaps
surprisingly, there is only one possibility if we try to solve ``:ps
97 vzipWith_rhs_2``:

.. code-block:: idris

    f x y :: vzipWith f xs ys

This works because ``vzipWith`` has a precise enough type: The
resulting vector has to be non-empty (a ``::``); the first element
must have type ``c`` and the only way to get this is to apply ``f`` to
``x`` and ``y``; finally, the tail of the vector can only be built
recursively.

:makewith
---------

The ``:makewith n f`` command, abbreviated ``:mw n f``, adds a
``with`` to a pattern clause. For example, recall ``parity``. If line
10 is:

.. code-block:: idris

    parity (S k) = ?parity_rhs

then ``:mw 10 parity`` will give:

.. code-block:: idris

    parity (S k) with (_)
      parity (S k) | with_pat = ?parity_rhs

If we then fill in the placeholder ``_`` with ``parity k`` and case
split on ``with_pat`` using ``:cs 11 with_pat`` we get the following
patterns:

.. code-block:: idris

      parity (S (plus n n)) | even = ?parity_rhs_1
      parity (S (S (plus n n))) | odd = ?parity_rhs_2

Note that case splitting has normalised the patterns here (giving
``plus`` rather than ``+``). In any case, we see that using
interactive editing significantly simplifies the implementation of
dependent pattern matching by showing a programmer exactly what the
valid patterns are.

Interactive Editing in Vim
==========================

The editor mode for Vim provides syntax highlighting, indentation and
interactive editing support using the commands described above.
Interactive editing is achieved using the following editor commands,
each of which update the buffer directly:

- ``\a`` adds a template definition for the name declared on the
   current line (using ``:addclause``).

- ``\c`` case splits the variable at the cursor (using
   ``:casesplit``).

- ``\m`` adds the missing cases for the name at the cursor (using
   ``:addmissing``).

- ``\w`` adds a ``with`` clause (using ``:makewith``).

- ``\s`` invokes a proof search to solve the hole under the
   cursor (using ``:proofsearch``).

There are also commands to invoke the type checker and evaluator:

- ``\t`` displays the type of the (globally visible) name under the
   cursor. In the case of a hole, this displays the context
   and the expected type.

- ``\e`` prompts for an expression to evaluate.

- ``\r`` reloads and type checks the buffer.

Corresponding commands are also available in the Emacs mode. Support
for other editors can be added in a relatively straightforward manner
by using ``idris2 -–client``.
More sophisticated support can be added by using the IDE protocol (yet to
be documented for Idris 2, but which mostly extends to protocol documented for
`Idris 1 <https://docs.idris-lang.org/en/latest/reference/ide-protocol.html>`_.
