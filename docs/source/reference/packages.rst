.. _ref-sect-packages:

********
Packages
********

Idris includes a simple system for building packages from a package
description file.  These files can be used with the Idris compiler to
manage the development process of your Idris programmes and packages.

Package Descriptions
====================

A package description includes the following:

+ A header, consisting of the keyword package followed by the package
  name. Package names can be any valid Idris identifier. The iPKG
  format also takes a quoted version that accepts any valid filename.
+ Fields describing package contents, ``<field> = <value>``

At least one field must be the modules field, where the value is a
comma separated list of modules.  For example, a library test which
has two modules ``Foo.idr`` and ``Bar.idr`` as source files would be
written as follows::

    package test

    modules = Foo, Bar

Other examples of package files can be found in the ``libs`` directory
of the main Idris repository, and in `third-party libraries <https://github.com/idris-lang/Idris-dev/wiki/Libraries>`_.

Metadata
--------

The `iPKG` format supports additional metadata associated with the package.
The added fields are:

+ ``brief = "<text>"``, a string literal containing a brief description
  of the package.

+ ``version = "<text>""``, a version string to associate with the package.

+ ``readme = "<file>""``, location of the README file.

+ ``license = "<text>"``, a string description of the licensing
  information.

+ ``authors = "<text>"``, the author information.

+ ``maintainers = "<text>"``, Maintainer information.

+ ``homepage = "<url>"``, the website associated with the package.

+ ``sourceloc = "<url>"``, the location of the DVCS where the source
  can be found.

+ ``bugtracker = "<url>"``, the location of the project's bug tracker.


Common Fields
-------------

Other common fields which may be present in an ``ipkg`` file are:

+ ``executable = <output>``, which takes the name of the executable
  file to generate. Executable names can be any valid Idris
  identifier. the iPKG format also takes a quoted version that accepts
  any valid filename.

  Executables are placed in ``build/exec``, relative to the top level
  source directory.

+ ``main = <module>``, which takes the name of the main module, and
  must be present if the executable field is present.

+ ``opts = "<idris options>"``, which allows options to be passed to
  Idris.

+ ``depends = <pkg name> (',' <pkg name>)+``, a comma separated list of
  package names that the Idris package requires.


Comments
---------

Package files support comments using the standard Idris singleline ``--`` and multiline ``{- -}`` format.

Using Package files
===================

Given an Idris package file ``test.ipkg`` it can be used with the Idris compiler as follows:

+ ``idris2 --build test.ipkg`` will build all modules in the package

+ ``idris2 --install test.ipkg`` will install the package, making it
  accessible by other Idris libraries and programs. Note that this doesn't
  install any executables, just library modules.

+ ``idris2 --clean test.ipkg`` will clean the intermediate build files.

Once the test package has been installed, the command line option
``--package test`` makes it accessible (abbreviated to ``-p test``).
For example::

    idris -p test Main.idr
