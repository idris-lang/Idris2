---
name: Installation Problem
about: Problem compiling or installing Idris 2
title: ""
labels: Installation Issue
assignees: ""
---

Please check INSTALL.md and README.md
to ensure you have all the required dependencies.
In particular,
you need a version of Chez Scheme compiled with threading support
(this is the default in most distributions)
in order to run the tests successfully.

Some common possible solutions:

- In `make bootstrap`,
  make sure you have the right executable name for `SCHEME`

- Stale `.ttc` files from an earlier version,
  or an out of data `IdrisPaths.idr`
  might be in the way.
  Try removing these
  with `make distclean`

- Removing all trace of Idris 2 from your installation directory might help.
  By default this is `$HOME/.idris2` -
  if you have a particularly out of date version,
  or you have used a broken build at some point
  (as much as we try to avoid this)
  then deleting this might help.

Otherwise,
please describe the problem,
including any relevant parts of build logs,
and describing as much about your environment as possible.
