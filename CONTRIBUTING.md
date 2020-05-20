Contributing to Idris 2
=======================

Contributions are welcome! The most important things needed at this stage,
beyond work on the language core, are (in no particular order):

* CI integration.
* Documentation string support (at the REPL and IDE mode).
* Generating HTML documentation from documentation strings (and possibly other
  formations)
* A better REPL, including:
  - `it` and `:let`
  - readline and tab completion
  - `:search` and `:apropos`
  - help commands
  - code colouring
  - it'd be nice if Ctrl-C didn't quit the whole system!
* IDE mode improvements
  - Syntax highlighting support for output 
  - Several functions from the version 1 IDE protocol are not yet implemented,
    and I haven't confirmed it works in everything.
  - (Not really part of Idris 2, but an editing mode for vim would be lovely!)
* Some parts of the Idris 1 Prelude are not yet implemented and should be
  added to base/
* Partial evaluation, especially for specialisation of interface 
  implementations.
* The lexer and parser are quite slow, new and faster versions with better
  errors would be good.
  - In particular, large sections commented out with {- -} can take a while
    to lex!
* An alternative, high performance, back end. OCaml seems worth a try.
* JS and Node back ends would be nice.

The default Prelude describes the rationale for what gets included and what
doesn't. Mostly what is there is copied from Idris 1, but it's not impossible
I've made some silly mistakes on the way. If you find any, please let me know
(or even better, submit a PR and a test case!).

Some language extensions from Idris 1 have not yet been implemented. Most
notably:

* Type providers
  - Perhaps consider safety - do we allow arbitrary IO operations, or is
    there a way to restrict them so that they can't, for example, delete
    files or run executables.
* Elaborator reflection
  - This will necessarily be slightly different from Idris 1 since the
    elaborator works differently. It would also be nice to extend it with
    libraries and perhaps syntax for deriving implementations of interfaces.
* `%default` directives, since coverage and totality checking have not been well
  tested yet.

Other contributions are also welcome, but I (@edwinb) will need to be
confident that I'll be able to maintain them!

If you're editing the core system, or adding any features, please keep an
eye on performance. In particular, check that the libraries build and tests
run in approximately the same amount of time before and after the change.
(Although running faster is fine as long as everything still works :))

Libraries
---------

Further library support would be very welcome, but unless it's adding something
that was in `prelude/` or `base/` in Idris 1, please add it initially into
`contrib/`. (We'll reorganise things at some point, but it will need some
thought and discussion).

Think about whether definitions should be `export` or `public export`. As
a general rule so far, type synonyms and anything where the evaluation
behaviour might be useful in a proof (so very small definitions) are
`public export` and everything else which is exported is `export`.

Syntax
------

Some syntax that hasn't yet been implemented but will be:

* Idiom brackets
* !-notation [needs some thought about the exact rules]

Some things from Idris 1 definitely won't be implemented:

* `%access` directives, because it's too easy to export things by accident
* Uniqueness types (instead, Idris 2 is based on QTT and supports linearity)
* Some esoteric syntax experiments, such as match applications
* Syntax extensions (at least in the unrestricted form from Idris 1)
* DSL blocks (probably) unless someone has a compelling use case that can't
  be done another way
