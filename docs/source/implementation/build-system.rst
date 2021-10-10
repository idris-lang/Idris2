*************************
The Build System of Idris
*************************

Introduction
------------

Compiling a compiler that is written in its own language (i.e. that is
*self-hosted*) is a somewhat trickier business than compiling other
applications. A `strange loop
<https://en.wikipedia.org/wiki/Strange_loop/>`_ forms when the
application that we are feeding in for the compiler is some version of
the compiler itself.

This process is called *bootstrapping*.

When we want to evolve our language/compiler, e.g. by adding a new language
feature, then we need to first implement it without assuming its existence, so
that the executable of our *bootstrap host* -- which of course has no clue about
the new feature yet --, can compile our sources. Once the new feature is working
(i.e. it is available as an executable binary, that we may call the *binary
seed*), then we can move to the next iteration of our language/compiler, and
start using the new feature in the next *evolutionary stage* of the language. At
this point we can even use the new feature in the implementation of the very
feature itself; our new language feature got fully *bootstrapped*. If you want
to explore this idea, then you may want to read the classic `Reflections on
Trusting Trust
<https://web.archive.org/web/20080731145744/http://cm.bell-labs.com/who/ken/trust.html/>`_
paper by Ken Thompson.

Idris compiles itself in the following consecutive stages, where each
stage is compiled by the previous stage:

* **stage 0** -- this is version ``n-1`` of the language/compiler. It
  is either provided by setting the ``BOOTSTRAP_IDRIS`` variable, or
  otherwise ``STAGE0_GIT_REF`` will be checked out under
  ``build/stage0/src-[git ref]``, and built using ``make
  bootstrap``. Only cleaned by ``make distclean``.

* **stage 1** -- version ``n`` of the sources compiled by version
  ``n-1``. This stage is not automatically rebuilt, only after a
  ``make clean``. The ``make bootstrap`` target compiles the stored
  build output of this stage (i.e. compile the checked in
  ``idris2.ss`` file using Chez) to produce an executable,
  i.e. doesn't need a working Idris executable. Let's call this trick
  a *bootstrap shortcut* (see `Bootstrap shortcuts`_ for details).

* **stage 2** -- these are the fully bootstrapped build artifacts, i.e.
  the output of version ``n`` compiling its own source. This target is
  forced (i.e. always rebuilt when invoked).

* **stage 3** -- this is an optional stage that mostly only needs to
  get built when we want to verify that the output of our compiler is
  reproducible, i.e. it repeatedly produces the same output for the
  same input (this can be done with the ``make check-reproducibility``
  makefile target).

Workflow
--------

TL;DR:

1) ``git clone``
2) edit ``config.mk``
3) ``make all``
4) ``make test``

(i.e. an external Idris executable is not necessary).

In normal, everyday development it is only stage 2 that gets rebuilt,
and used as a driver for running the tests.

When ``STAGE0_GIT_REF`` is empty (which should be the default in the
repo), then ``make all`` (or simply ``make``) will take a bootstrap
shortcut.

If you want to **make an evolutionary step** of the language
(i.e. regenerate the stage 1 build artifacts, aka the *bootstrap
shortcut*), then you will need a working stage 0. This is not strictly
necessary, because stage 1 can also be produced by using a
bootstrapped stage 1 to compile stage 2, and then copying the stage 2
build artifacts using ``make prepare-bootstrap-files``. But that way
you wouldn't notice if version ``n-1`` was not able to compile version
``n`` anymore, i.e. when some change broke the bootstrappability
chain.

You can make an evolutionary step in two similar ways:

1) by setting the ``BOOTSTRAP_IDRIS`` variable to point to a working
   Idris binary, or

2) by setting the ``STAGE0_GIT_REF`` variable in your local makefile
   to point to a git tag or branch. Doing so will instruct the
   makefile to check out, bootstrap, and use that git ref as stage 0,
   i.e. use it as bootstrap host to regenerate the stage 1 build
   artifacts.

Once stage 2 is built, you can use the ``make
prepare-bootstrap-files`` to prepare them, and add them to the git
index, i.e. ready to be committed.

``make clean`` does not delete ``build/stage0`` (only ``make
distclean`` does), because the bootstrap compiler is not affected by
any changes made to *our* sources.

``make clean`` only deletes stage 1 when either ``STAGE0_GIT_REF`` or
``BOOTSTRAP_IDRIS`` is set, becuase stage 1 cannot be regenerated
without a valid stage 0, and thus in those configurations stage 1 gets
bootstrapped from the checked in bootstrap shortcut files.

Language evolution vs. releases
-------------------------------

Having made a new evolutionary step in the language doesn't
necessarily mean that we also want to stamp its implementation as a
public release. Therefore, we branch off every new evolutionary stage
into an ``idris.[consecutive stage number]`` git branch, and use git
tags independently for stamping public releases. The consequtive
branches are the evolutionary stages of the language that can
bootstrap each other in a row. The git release tags are the versions
that we want to disseminate to our users.

Note on nomenclature: an *evolutionary stage* is different from a
*stage*: the former is a new version of the language, the latter is a
new stage of the compiler compiling itself. Suggestions for a better
nomenclature are welcome.

Assorted benefits of this setup:

* we can go back and patch older versions and keep them bootstrappable
  all the way back until Idris v1.3.4 that is written in Haskell.

* this way it's `bootstrappable <http://bootstrappable.org//>`_!

* enables experimenting with other ways to bootstrap Idris than the
  original Haskell implementation; e.g. someone may venture into
  writing a subset of Idris in another language that is good enough to
  compile Idris proper. If we store this in a branch, then we can
  retain a shorter path to bootstrappability than all the way back
  from GHC.

Implementation
--------------

Each stage is built and installed in a directory under
``build/stage[n]``, and can be built by ``make sage0`` .. ``make
stage3``.

The version of stage 0 is selected by the ``STAGE0_GIT_REF`` variable,
and can point to any git ref, including branches.

All build output is produced under ``build/`` (for now the exceptions
are ``IdrisPaths.idr`` and the output of the tests).

The makefile is split into two parts:

* ``Makefile.one-stage`` contains the common parts that build a stage.

* ``Makefile`` is the main makefile that manages the chaining of the
  build stages, among other things by invoking (calling) the
  ``Makefile.one-stage`` sub-makefile with varying parameters, and
  potentially multiple times.

Bootstrap shortcuts
-------------------

If we need version ``n-1`` to build us, and if ``n-1`` needs ``n-2``,
then we quickly find ourselves all the way back at Idris v1.3.4, the
last version in the now mostly abandoned v1 line of Idris, that was
written in Haskell, and thus can be compiled using GHC.

If we want to avoid this, then we can make a *bootstrap shortcut*: if
we check in e.g. the output of the *chez* backend (a Scheme file) into
the Idris repo, then all we need to produce a working Idris binary is
a working ``chez-scheme`` binary to compile it for us.

The makefile is set up so that you can simply ``git add`` the ``.ss``
and ``.rkt`` backend output files (hint: ``make
prepare-bootstrap-files``), and then ``git commit`` them into the
repo. The ``make bootstrap`` target then ``git checkout build/`` the
bootstrap shortcut files, and produces the stage 1 executable by
simply compiling the intermediate output of one of the CG backends
using the ``chez-scheme`` binary, or Racket's ``raco`` binary (as
opposed to invoking Idris version ``n-1``). The CG to be used for the
bootstrap is selected by the usual ``IDRIS2_CG`` variable.
