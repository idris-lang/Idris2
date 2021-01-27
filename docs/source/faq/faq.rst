**************************
Frequently Asked Questions
**************************

Can Idris 2 compile itself?
===========================

Yes, Idris 2 is implemented in Idris 2. By default, it targets
`Chez Scheme <https://cisco.github.io/ChezScheme/>`_, so you can bootstrap
from the generated Scheme code, as described in Section :ref:`sect-starting`.

Why does Idris 2 target Scheme? Surely a dynamically typed target language is going to be slow?
===============================================================================================

You may be surprised at how fast Chez Scheme is :). `Racket <https://download.racket-lang.org/>`_,
as an alternative target, also performs well. Both perform better than the
Idris 1 back end, which is written in C but has not had the decades of
engineering effort by run time system specialists that Chez and Racket have.
Chez Scheme also allows us to turn off run time checks, which we do.

As anecdotal evidence of the performance improvement, as of 23rd May 2020, on a
Dell XPS 13 running Ubuntu, the performance is:

* Idris 2 (with the Chez Scheme runtime) checks its own source in 93 seconds.
* The bootstrapping Idris 2 (compiled with Idris 1) checks the same source in 125s.
* Idris 1 checks the bootstrapping Idris 2's source (the same as the above,
  but with minor variations due to the syntax changes) in 768 seconds.

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
Section :ref:`sect-multiplicities`, we can write more precise types in the
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

The Idris2 repl does not support readline in the interest of
keeping dependencies minimal. A useful work around is to
install `rlwrap <https://linux.die.net/man/1/rlwrap>`_, this
utility provides command history simply by invoking the Idris2
repl as an argument to the utility ``rlwrap idris2``.

The goal, eventually, is to use the IDE mode as the basis of an implementation
of a sophisticated REPL, developed independently from the Idris 2 core.

Where can I find more answers?
==============================

The `Idris 1 FAQ <https://docs.idris-lang.org/en/latest/faq/faq.html>`_ is
mostly still relevant.
