Contributing to Idris 2
=======================

We welcome contributions! This document describes how you can contribute to
Idris 2, and the kind of contributions which will most benefit the project.

Please remember when making contributions via pull requests, though, that Idris
is primarily a research project, and we are a small team, which limits the time
we have available for reviewing and maintaining PRs. Nobody works full time on
Idris - we're a team of academics and students at a university with other
demands on our time such as teaching, and writing and presenting research
papers, which will always take priority. This also means we have to be careful
to make sure that we can commit to maintaining any new features which are
contributed.

This document outlines: the kinds of contributions we will almost certainly
accept; those we might accept; those we might accept after a proposal and
discussion; and, those we almost certainly won't. The guidelines here are based
on decisions we've previously made, and the way we have managed PRs in practice
up to now.

General comments
----------------

Overall, when making a contribution, please try to make sure they follow the
general philosophy of the Idris project, which can be summarised as follows:

* Idris aims to make advanced type-related programming techniques accessible to
  software practitioners
* Idris *allows* software developers to express invariants of their data and prove
  properties of programs, but will not *require* them to do so

Many contributions will require accompanying tests and documentation updates.
Bugfixes in particular should be accompanied by tests, to avoid future
regressions.

Library functions should be `total` as far as possible, and at least `covering`
where `total` is not possible.

Different people have different preferences about coding style. In general,
we haven't been too prescriptive about this. If you're editing a source file,
try to be consistent with the existing style choices made by previous authors.
We may need to be more formal about this in future!

Please remember to update `CHANGELOG.md`, and if it's your first contribution
you can add yourself to `CONTRIBUTORS`.

In all cases, a pull request must have a short description (one sentence is
usually enough) that explains its purpose. However obvious you think it might
be, it really helps when reviewing the changes.

Things we will almost certainly accept
--------------------------------------

* Anything which fixes an issue on the issue tracker
  - In this case, please make sure you include a new test
* More tests, which test new features or, more importantly, existing features
  which are not exercised enough in the existing tests
  - Note that the 'test' subdirectory is intended for testing the type checker
    and compiler, not specifically for testing libraries. However, we do need
    a better way of testing libraries! (More on this below)
* Rewrites of existing features which demonstrably improve performance
* Documentation, and improvements to documentation generation tools
* Improvements to existing tool support, including:
  - Type-driven program synthesis
  - :search and related REPL commands
  - Interactive editing
* Contributions of missing library functions, including proofs, which were
  available in Idris 1 - at least on the assumption that we still think the
  function is important enough, which gets increasingly unlikely over time!

Things we might accept
----------------------

* Additions to the `contrib` libraries
  - However, please consider whether it would be better as a separate library.
    If something is in the Idris2 repository, we need to commit to maintaining
    it to some extent, so we have to be sure that we can do so. You can find
    (and contribute to) a list of [libraries on the wiki](
    https://github.com/idris-lang/Idris2/wiki/1-%5BLanguage%5D-Libraries).
  - For any library additions, please try to include as many documentation
    strings as you can.

Things that should be discussed via the issue tracker first
-----------------------------------------------------------

* New language features
  - Syntactic sugar, for example, is nice but any new feature needs to be
    worth the additional burden it places on programmers learning the language
* Changes to any of the core representations (TT and CExp in particular)
  - These have been fairly stable for a while, and external tools using the
    Idris 2 API may be depending on them
* Changes to prelude and base libraries
  - 'prelude' and 'base' are, in some sense, part of the language. There are a
    lot of trade offs to be made in the design of the prelude especially - such
    as interface hierarchies - and while you may not agree with the way it looks,
    by and large these decisions have already been made so there must be a
    compelling reason for them to be changed.
* Any fundamental changes to build system, library structure, or CI workflow
* Major refactorings (e.g. reorganisation of imports, mass renamings). These
  may be a good idea, but they are often merely a matter of taste, so please
  check whether they will be considered valuable first.
* A new approach to testing libraries: we don't have a unit testing or
  property testing framework as part of the Idris system, itself, though it
  would be valuable for testing the prelude and base libraries. This would be
  nice to have, so proposals are welcome.

Things we probably won't accept
-------------------------------

* Minor refactorings. You may be making the code more beautiful, or more to
  your taste, but please remember that every PR has to be reviewed, and if it
  takes more time to run the tests and review it than it took to make the change,
  it's costing us time rather than saving it.
  - On the other hand, tidying up code as part of a larger PR is very welcome.
    We encourage following the camp site rule: leave the code tidier than you
    found it!
* Primitive updates without a strong justification
  - Primitives increase the burden on backend authors, for example. They may
    be necessary to support a new library, if a foreign function call is not
    appropriate, but we won't accept a primitive on the basis that it could be
    useful in future.
* Requests to migrate libraries from `contrib` to `base`. We do need to
  organise libraries better, but this will be better achieved with a good
  package manager.
* Fancy REPL features (e.g. readline, history, tab completion). We definitely
  want this, but it would be better implemented as a separate tool using the
  Idris 2 API, to minimise the maintenance burden on the compiler.
* Similarly, anything which adds an external dependency. We aim to keep
  dependencies minimal for ease of initial installation.
* New backends. You can implement new backends via the Idris 2 API - and indeed
  several people have. The backends in this repository are limited to those we
  are able to commit to maintaining.

Other possible contributions
----------------------------

There's plenty of other things that might be good ideas. If it isn't covered
above, and you're in doubt as to whether it might be a good idea, please let us
know that you're considering it and we can discuss how well it will fit. Please
just remember that whatever you contribute, we have to maintain!

Good places to discuss possible contributions are:

* The [mailing list](https://groups.google.com/forum/#!forum/idris-lang).
* The Idris community on Discord [(invite link)](https://discord.gg/YXmWC5yKYM).
* The issue tracker (in this case, please make your proposal as concrete as
  possible).

On performance
--------------

If you're editing the core system, or adding any features, please keep an
eye on performance. In particular, check that the libraries build and tests
run in approximately the same amount of time before and after the change.
(Although running faster is fine as long as everything still works :))
