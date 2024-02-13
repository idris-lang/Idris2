**************************
Frequently Asked Questions
**************************

What are the aims of the Idris project?
=======================================

Idris aims to make advanced type-related programming techniques accessible to
software practitioners. An important philosophy that we follow is that
Idris *allows* software developers to express invariants of their data and
prove properties of programs, but will not *require* them to do so.

Many of the answers in this FAQ demonstrate this philosophy, and we always
bear this in mind when making language and library design decisions.

Idris is primarily a research project, led by Edwin Brady at the University
of St Andrews, and has benefited from `SICSA <https://www.sicsa.ac.uk>`_ and
`EPSRC <https://www.epsrc.ac.uk/>`_ funding. This does influence some design
choices and implementation priorities, and means that some things are not
as polished as we'd like. Nevertheless, we are still trying to make it as
widely usable as we can!

Where can I find libraries? Is there a package manager?
=======================================================

Idris doesn't have an official package manager, but there are a number of
community-maintained package managers
`listed on the wiki <https://github.com/idris-lang/Idris2/wiki/Third-party-Libraries#package-management>`_
(`pack <https://github.com/stefan-hoeck/idris2-pack>`_ is particularly widely
used and actively maintained). On that page you can also find a number of
community libraries.

Can Idris 2 compile itself?
===========================

Yes, Idris 2 is implemented in Idris 2. By default, it targets
`Chez Scheme <https://cisco.github.io/ChezScheme/>`_, so you can bootstrap
from the generated Scheme code, as described in Section :ref:`sect-starting`.

Why does Idris 2 target Scheme? Surely a dynamically typed target language is going to be slow?
===============================================================================================

You may be surprised at how fast Chez Scheme is! `Racket <https://download.racket-lang.org/>`_,
as an alternative target, also performs well. Both perform better than the
Idris 1 back end, which is written in C but has not had the decades of
engineering effort by run time system specialists that Chez and Racket have.
Chez Scheme also allows us to turn off run time checks, which we do.

As anecdotal evidence of the performance improvement, we compared the
performance of the Idris 2 runtime with the Idris 1 runtime, using a version of
the compiler built with the Chez runtime and the same version built with the
bootstrapping Idris 2.  On a Dell XPS 13 running Ubuntu, with the versions of
23rd May 2020, the performance was:

* Idris 2 (with the Chez Scheme runtime) checked its own source in 93 seconds.
* The bootstrapping Idris 2 (compiled with Idris 1) checked the same source in 125s.
* Idris 1 checked the bootstrapping Idris 2's source (the same as the above,
  but with minor variations due to the syntax changes) in 768 seconds.

Unfortunately we can't repeat this experiment with the latest version, since
the bootstrapping Idris 2 is no longer able to build the current version.

This is, nevertheless, not intended to be a long term solution, even if it
is a very convenient way to bootstrap.

Can Idris 2 generate Javascript? What about plug-in code generators?
====================================================================

Yes! A `JavaScript code generator <https://idris2.readthedocs.io/en/latest/backends/javascript.html>`_
is built in, and can target either the browser or NodeJS.

Like Idris 1, Idris 2
`supports plug-in code generation <https://idris2.readthedocs.io/en/latest/backends/custom.html>`_
to allow you to write a back end for the platform of your choice.

What are the main differences between Idris 1 and Idris 2?
==========================================================

The most important difference is that Idris 2 explicitly represents *erasure*
in types, so that you can see at compile time which function and data type
arguments are erased, and which will be present at run time. You can see more
details in :ref:`sect-multiplicities`.

Idris 2 has significantly better type checking performance (perhaps even an
order of magnitude!) and generates significantly better code.

Also, being implemented in Idris, we've been able to take advantage of the
type system to remove some significant sources of bugs!

You can find more details in Section :ref:`updates-index`.

Why aren't there more linearity annotations in the library?
===========================================================

In theory, now that Idris 2 is based on Quantitative Type Theory (see
Section :ref:`sect-multiplicities`), we can write more precise types in the
Prelude and Base libraries which give more precise usage information. We have
chosen not to do that (yet) however. Consider, for example, what would happen
if we did::

    id : (1 _ : a) -> a
    id x = x

This is definitely correct, because ``x`` is used exactly once. However, we
also have::

    map : (a -> b) -> List a -> List b

We can't guarantee that the function passed to ``map`` is linear in its
argument in general, and so we can no longer say ``map id xs`` since the
multiplicity of ``id`` doesn't match the multiplicity of the function passed
to ``map``.

Eventually, we hope to extend the core language with multiplicity polymorphism
which will help resolve these problems. Until then, we consider linearity an
experimental new feature in the type system, and therefore we follow the general
philosophy that if you don't want to use linearity, its presence mustn't
impact the way you write programs.

How do I get command history in the Idris2 REPL?
================================================

The Idris2 REPL does not support readline in the interest of
keeping dependencies minimal. A useful work around is to
install `rlwrap <https://linux.die.net/man/1/rlwrap>`_, this
utility provides command history simply by invoking the Idris2
repl as an argument to the utility ``rlwrap idris2``.

The goal, eventually, is to use the IDE mode or the Idris API as the basis of
an implementation of a sophisticated REPL, developed independently from the
Idris 2 core. As far as we know, nobody is yet working on this: if you're
interested, please get in touch and we can help you get started!

Why does Idris use eager evaluation rather than lazy?
=====================================================

Idris uses eager evaluation for more predictable performance, in particular
because one of the longer term goals is to be able to write efficient and
verified low level code such as device drivers and network infrastructure.
Furthermore, the Idris type system allows us to state precisely the type
of each value, and therefore the run-time form of each value. In a lazy
language, consider a value of type ``Int``:

.. code-block:: idris

    thing : Int

What is the representation of ``thing`` at run-time? Is it a bit pattern
representing an integer, or is it a pointer to some code which will compute
an integer? In Idris, we have decided that we would like to make this
distinction precise, in the type:

.. code-block:: idris

    thing_val : Int
    thing_comp : Lazy Int

Here, it is clear from the type that ``thing_val`` is guaranteed to be a
concrete ``Int``, whereas ``thing_comp`` is a computation which will produce an
``Int``.

How can I make lazy control structures?
=======================================

You can make control structures using the special Lazy type. For
example, one way to implement a non-dependent ``if...then...else...``
would be via a function named ``ifThenElse``:

.. code-block:: idris

    ifThenElse : Bool -> (t : Lazy a) -> (e : Lazy a) -> a
    ifThenElse True  t e = t
    ifThenElse False t e = e

The type ``Lazy a`` for ``t`` and ``e`` indicates that those arguments will
only be evaluated if they are used, that is, they are evaluated lazily.

By the way: we don't actually implement ``if...then...else...`` this way in
Idris 2! Rather, it is transformed to a ``case`` expression which allows
dependent ``if``.

Evaluation at the REPL doesn't behave as I expect. What's going on?
===================================================================

Being a fully dependently typed language, Idris has two phases where it
evaluates things, compile-time and run-time. At compile-time it will only
evaluate things which it knows to be total (i.e. terminating and covering all
possible inputs) in order to keep type checking decidable. The compile-time
evaluator is part of the Idris kernel, and is implemented as an interpreter
in Idris. Since everything is known to have a normal form here, the evaluation
strategy doesn't actually matter because either way it will get the same
answer! In practice, it uses call by name, since this avoids evaluating
sub-expressions which are not needed for type checking.

The REPL, for convenience, uses the compile-time notion of evaluation. As well
as being easier to implement (because we have the evaluator available) this can
be very useful to show how terms evaluate in the type checker. So you can see
the difference between:

.. code-block:: idris

    Main> \n, m => S n + m
    \n, m => S (plus n m)

    Main> \n, m => n + S m
    \n, m => plus n (S m)

If you want to compile and execute an expression at the REPL, you can use
the ``:exec`` command. In this case, the expression must have type ``IO a``
(for any ``a``, although it won't print the result).

Why can't I use a function with no arguments in a type?
=======================================================

If you use a name in a type which begins with a lower case letter, and which is
not applied to any arguments, then Idris will treat it as an implicitly
bound argument. For example:

.. code-block:: idris

    append : Vect n ty -> Vect m ty -> Vect (n + m) ty

Here, ``n``, ``m``, and ``ty`` are implicitly bound. This rule applies even
if there are functions defined elsewhere with any of these names. For example,
you may also have:

.. code-block:: idris

    ty : Type
    ty = String

Even in this case, ``ty`` is still considered implicitly bound in the definition
of ``append``, rather than making the type of ``append`` equivalent to...

.. code-block:: idris

    append : Vect n String -> Vect m String -> Vect (n + m) String

...which is probably not what was intended!  The reason for this rule is so
that it is clear just from looking at the type of ``append``, and no other
context, what the implicitly bound names are.

If you want to use an unapplied name in a type, you have three options. You
can either explicitly qualify it, for example, if ``ty`` is defined in the
namespace ``Main`` you can do the following:

.. code-block:: idris

    append : Vect n Main.ty -> Vect m Main.ty -> Vect (n + m) Main.ty

Alternatively, you can use a name which does not begin with a lower case
letter, which will never be implicitly bound:

.. code-block:: idris

    Ty : Type
    Ty = String

    append : Vect n Ty -> Vect m Ty -> Vect (n + m) Ty

As a convention, if a name is intended to be used as a type synonym, it is
best for it to begin with a capital letter to avoid this restriction.

Finally, you can turn off the automatic binding of implicits with the
directive:

.. code-block:: idris

    %unbound_implicits off

In this case, you can bind ``n`` and ``m`` as implicits, but not ``ty``,
as follows:

.. code-block:: idris

    append : forall n, m . Vect n ty -> Vect m ty -> Vect (n + m) ty

Why don't the ``Functor``, ``Applicative``, ``Monad`` and other interfaces include the laws?
============================================================================================

On the face of it, this sounds like a good idea, because the type system allows
us to specify the laws. We don't do this in the prelude, though, for two
main reasons:

* It goes against the philosophy (above) that Idris *allows* programmers to
  prove properties of their programs, but does not *require* it.
* A valid, lawful, implementation may not necessarily be provably lawful
  within the Idris system, especially if it involves higher order functions.

There are verified versions of the interfaces in ``Control.Algebra``, which
extend interfaces with laws.

I have an obviously terminating program, but Idris says it possibly isn't total. Why is that?
=============================================================================================

Idris can't decide in general whether a program is terminating due to
the undecidability of the `Halting Problem
<https://en.wikipedia.org/wiki/Halting_problem>`_. It is possible, however,
to identify some programs which are definitely terminating. Idris does this
using "size change termination" which looks for recursive paths from a
function back to itself. On such a path, there must be at least one
argument which converges to a base case.

- Mutually recursive functions are supported

- However, all functions on the path must be fully applied. In particular,
  higher order applications are not supported

- Idris identifies arguments which converge to a base case by looking for
  recursive calls to syntactically smaller arguments of inputs. e.g.
  ``k`` is syntactically smaller than ``S (S k)`` because ``k`` is a
  subterm of ``S (S k)``, but ``(k, k)`` is
  not syntactically smaller than ``(S k, S k)``.

If you have a function which you believe to be terminating, but Idris does
not, you can either restructure the program, or use the ``assert_total``
function.

Does Idris have universe polymorphism? What is the type of ``Type``?
====================================================================

Idris 2 currently implements ``Type : Type``. Don't worry, this will not be the
case forever! For Idris 1, the FAQ answered this question as follows:

Rather than universe polymorphism, Idris has a cumulative hierarchy of
universes; ``Type : Type 1``, ``Type 1 : Type 2``, etc.
Cumulativity means that if ``x : Type n`` and ``n <= m``, then
``x : Type m``. Universe levels are always inferred by Idris, and
cannot be specified explicitly. The REPL command ``:type Type 1`` will
result in an error, as will attempting to specify the universe level
of any type.

What does the name “Idris” mean?
================================

British people of a certain age may be familiar with this
`singing dragon
<https://web.archive.org/web/20160531194307/https://www.youtube.com/watch?v=G5ZMNyscPcg>`_.
If that doesn’t help, maybe you can invent a suitable acronym :-) .

Where can I find the community standards for the Idris community?
==================================================================

The Idris Community Standards are stated `here
<https://www.idris-lang.org/pages/community-standards.html>`_

