Contributing to Idris 2
=======================

We welcome contributions! This document describes how you can contribute to
Idris 2, and the kind of contributions which will most benefit the project.

This document outlines: the kinds of contributions we will almost certainly
accept; those we might accept; those we might accept after a proposal and
discussion; and, those we almost certainly won't. The guidelines here are based
on decisions we've previously made, and the way we have managed PRs in practice
up to now.

## Disclaimer

Please remember that Idris
is primarily a research project, and we are a small team, which limits the time
we have available for reviewing and maintaining PRs. Nobody works full time on
Idris - we're a team of volunteers, academics, and students with other
demands on our time such as teaching, and writing and presenting research
papers, which will always take priority. This means that we have a limited
capacity to review and accept contributions and we cannot commit to maintain
any new features which are contributed.


## General comments

Overall, when making a contribution, please try to make sure they follow the
general philosophy of the Idris project, which can be summarised as follows:

* Idris aims to make advanced type-related programming techniques accessible to
  software practitioners.
* Idris *allows* software developers to express invariants of their data and prove
  properties of programs, but will not *require* them to do so.


### Guidlines for Writing Issues

When writing an issue and describing the problem at hand, avoid linking to
private channels of discussions such as Discord. Other contributors might not
have an account, the servers could be down, the information might be hard to
find, or some people might not be able to use the service from their devices.
Instead, write a clear summary of the situation so that anyone can
understand what the issue is about without additional context.

### Guidlines for Pull Requests

Many contributions will require accompanying tests and documentation updates.
Bugfixes in particular should be accompanied by tests, to avoid future
regressions.

Library functions should be `total` as far as possible, and at least `covering`
where `total` is not possible. They should come with appropriate documentation
and examples for how to use them.

Different people have different preferences about coding style. In general,
we haven't been too prescriptive about this. If you're editing a source file,
try to be consistent with the existing style choices made by previous authors.
We may need to be more formal about this in future!

Please remember to update `CHANGELOG_NEXT.md`, and if it's your first contribution
you can add yourself to `CONTRIBUTORS`.

In all cases, a pull request must have a short description that explains its purpose.
However obvious you think it might be, it really helps reviewers know what to look for
when reviewing the changes. A reviewer does not have to be an Idris maintainer and
could be any other knowledgable community member.

## Things We Will Almost Certainly Accept

* Anything which fixes an issue on the issue tracker
  - For bugfixes, please make sure you include a new test for it.
  - This is a good way to get your change included since it tremendously helps
    with reviewing.
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

## Things That Should Be Discussed via the Issue Tracker First

* New language features
  - Syntactic sugar, for example, is nice but any new feature needs to be
    worth the additional burden it places on programmers learning the language
* Changes to any of the core representations (TT and CExp in particular)
  - These have been fairly stable for a while, and external tools using the
    Idris 2 API may be depending on them
* Changes to prelude and base libraries
  - `prelude` and `base` are, in some sense, part of the language. There are a
    lot of trade offs to be made in the design of the prelude especially - such
    as interface hierarchies - and while you may not agree with the way it looks,
    by and large these decisions have already been made so there must be a
    compelling reason for them to be changed.
* Changes to elaborator script compatibility. Elaborator Reflection is a feature
  powering some of the most important libraries in the ecosystem and breaking
  them breaks the entire ecosystem of libraries. Changes to Elaborator Reflection
  therefore requires careful coordination between PR author, and library maintainers.
* Any fundamental changes to build tools, library structure, or CI workflow
* Major refactorings (e.g. reorganisation of imports, mass renamings). These
  may be a good idea, but they are often merely a matter of taste, so please
  check whether they will be considered valuable first.

## Things We Probably Won't Accept

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
* Anything which adds an external dependency. We aim to keep
  dependencies minimal for ease of initial installation.
* New backends. You can implement new backends via the Idris 2 API - and indeed
  several people have. The backends in this repository are limited to those we
  are able to commit to maintaining.

## Other possible contributions

There's plenty of other things that might be good ideas. If it isn't covered
above, and you're in doubt as to whether it might be a good idea, please let us
know that you're considering it and we can discuss how well it will fit. Please
just remember that whatever you contribute, we have to maintain!

Good places to discuss possible contributions are:

* The [mailing list](https://groups.google.com/forum/#!forum/idris-lang).
* The Idris community on Discord [(invite link)](https://discord.gg/YXmWC5yKYM).
* The issue tracker (in this case, please make your proposal as concrete as
  possible).

## On performance

If you're editing the core system, or adding any features, please keep an
eye on performance. In particular, check that the libraries build and tests
run in approximately the same amount of time before and after the change.
(Although running faster is fine as long as everything still works :))

## Guidelines for Maintainers & Self-Merge Policy

Maintainers can self-merge some of their PR under certain conditions. This
acknowledges the fact that not everyone is able to review everything in a timely
manner and reviewers are already trusted entities able to check-in code in the
project. However, it should be done with care and consideration, self-merge is
acceptable provided it:

* Does not break any libraries in the overall ecosystem
* Does not significantly impact performance
* Does not break or change CI in any fundamental way (disabling tests for example)

If any of the above conditions are not met, self-merge is to be avoided.

Before performing a self-merge, maintainers are expected to perform a self-review
held to the same standards as any other pull request and check for:
* Missing documentation
* Missing tests
* Appropriate code styling
* Appropriate description and motivation
* Appropriate updates to the changelog

Please leave 7 days from the date of PR submission until performing a self-merge.
