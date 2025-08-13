.. _ref-sect-packages:

********
Packages
********

Idris includes a system for building packages from a package
description file.  These files can be used with the Idris compiler to
manage the development process of your Idris programs and packages.

Package Descriptions
====================

A package description includes the following:

+ A header, consisting of the keyword ``package`` followed by the package
  name. Package names can be any valid Idris identifier. The iPKG
  format also takes a quoted version that accepts any valid filename.
+ Fields describing package contents, ``<field> = <value>``

Packages can describe libraries, executables, or both, and should include
a version number. For library packages,
one field must be the modules field, where the value is a comma separated list
of modules to be installed. For example, a library ``test`` which has two modules
``Foo.idr`` and ``Bar.idr`` as source files would be written as follows::

    package test
    version = 0.0.1

    modules = Foo, Bar

When installed, this will be in a directory ``test-0.1``. If the version
number is missing, it will default to ``0``.

Other examples of package files can be found in the ``libs`` directory
of the main Idris repository, and in `third-party libraries <https://github.com/idris-lang/Idris2/wiki/Third-party-Libraries>`_.

Metadata
--------

The `iPKG` format supports additional metadata associated with the package.
The added fields are:

+ ``brief = "<text>"``, a string literal containing a brief description
  of the package.

+ ``version = <version number>``, a semantic version number, which must be in the form
  of integers separated by dots (e.g. ``1.0.0``, ``0.3.0``, ``3.1.4`` etc)

+ ``langversion <version constraints>``, see ``depends`` below for a list of allowable
  constraints. For example, ``langversion >= 0.5.1 && < 1.0.0``

+ ``readme = "<file>"``, location of the README file.

+ ``license = "<text>"``, a string description of the licensing
  information.

+ ``authors = "<text>"``, the author information.

+ ``maintainers = "<text>"``, Maintainer information.

+ ``homepage = "<url>"``, the website associated with the package.

+ ``sourceloc = "<url>"``, the location of the DVCS where the source
  can be found.

+ ``bugtracker = "<url>"``, the location of the project's bug tracker.

Directories
-----------

+ ``sourcedir = "<dir>"``, the directory to look for Idris source files.

+ ``builddir = "<dir>"``, the directory to put the checked modules and
  the artefacts from the code generator.

+ ``outputdir = "<dir>"``, the directory where the code generator should
  output the executable.

Common Fields
-------------

Other common fields which may be present in an ``ipkg`` file are:

+ ``executable = <output>``, which takes the name of the executable
  file to generate. Executable names can be any valid Idris
  identifier. the iPKG format also takes a quoted version that accepts
  any valid filename.

  Executables are placed in ``build/exec`` by default. The location can
  be changed by specifying the ``outputdir`` field.

+ ``main = <module>``, which takes the name of the main module, and
  must be present if the ``executable`` field is present.

+ ``opts = "<idris options>"``, which allows options to be passed to
  Idris.

+ ``depends = <pkg description> (',' <pkg description>)+``, a comma separated list of
  package names that the Idris package requires. The ``pkg_description`` is
  the package name, followed by an optional list of version constraints. Version
  constraints are separated by ``&&`` and can use operators
  ``<``, ``<=``, ``>``, ``>=``, ``==``. For example, the following are valid
  package descriptions:

    - ``contrib`` (no constraints)

    - ``contrib == 0.3.0`` (an exact version constraint)

    - ``contrib >= 0.3.0`` (an inclusive lower bound)

    - ``contrib >= 0.3.0 && < 0.4`` (an inclusive lower bound, and exclusive upper bound)



Comments
---------

Package files support comments using the standard Idris singleline ``--`` and multiline ``{- -}`` format.

Using Package files
===================

Given an Idris package file ``test.ipkg`` it can be used with the Idris compiler as follows:

+ ``idris2 --build test.ipkg`` will build all modules in the package

+ ``idris2 --install test.ipkg`` will install the package to the global
  Idris library directory (that is ``$IDRIS2_PREFIX/idris-<version>/``),
  making the modules in its ``modules`` field accessible by other Idris
  libraries and programs. Note that this doesn't install any executables, just
  library modules.

+ ``idris2 --clean test.ipkg`` will clean the intermediate build files.

+ ``idris2 --mkdoc test.ipkg`` will generate HTML documentation for the
  package, output to ``build/docs``

Once the test package has been installed, the command line option
``--package test`` makes it accessible (abbreviated to ``-p test``).
For example::

    idris -p test Main.idr

Where does Idris look for packages?
===================================

Compiled packages are directories with compiled TTC files (see :ref:`build-artefacts` section).
Directory structure of the source `*.idr` files is preserved for TTC files.

Compiled packages can be installed globally (under ``$IDRIS2_PREFIX/idris-<version>/`` as
described above) or locally (under a ``depends`` subdirectory in the top level
working directory of a project).
Packages specified using ``-p pkgname`` or with the ``depends`` field of a
package will then be located as follows:

* First, Idris looks in ``depends/pkgname-<version>``, for a package which
  satisfies the version constraint.
* If no package is found locally, Idris looks in
  ``$IDRIS2_PREFIX/idris-<version>/pkgname-<version>``.

In each case, if more than one version satisfies the constraint, it will choose
the one with the highest version number.
If package versions are omitted in directory names, they are treated as the version ``0``.

Support file install directories
================================

As noted above, packages can be installed globally or locally to be used as dependencies in
other projects. In either case, there are two directories within a package's install root that
Idris 2 treats specially when the package is depended upon by some other Idris package.

Those directories are ``lib`` and ``data``.

Below we will refer to these directories as ``pkgname-<version>/lib`` and ``pkgname-<version>/data``
and in all cases these folders may be located locally in the depending project within a ``depends``
directory or globally (you can ask Idris 2 for the global install directory with ``idris2 --libdir``).

Library files
-------------

Idris will look for library files at ``pkgname-<version>/lib``. Library files are those that
will need to be around whenever an executable that depends on your library is run. That is,
these files are not built into the executable, but rather linked against or otherwise referred
to during building and then loaded in at runtime. A common example of this type of file is a
shared object file (these commonly have the extension ``.so`` on Linux systems and ``.dylib`` on Mac OS
systems).

When building with the Scheme or Refc backends, you may want your package to use Idris 2's ``C`` FFI
and rely on a ``C`` support file. The FFI interface is documented elsewhere so we won't go into that
here. Once you do have a support file written in ``C``, you can build an ``so`` file using your
package's post-build hook. Then, install (copy) that ``so`` file into the ``lib`` subfolder where
Idris has installed your package in your post-install hook. When an executable depends on your package,
Idris will copy shared object files from the ``lib`` directory into the build folder for the executable.

Data files
----------

Idris will look for data files at ``pkgname-<version>/data``. Data files are a bit open-ended
in how they are used. One important use-case is adding support files for the ``Javascript`` FFI.
``Javascript`` support files are different from ``C`` support files in that they get built *into* the
executable rather than installed alongside it. The FFI interface is documented elsewhere, but we will
briefly touch on the subject to describe the end-to-end packaging of JS support files using the
``data`` directory.

When building with the NodeJS backend, you can refer to functions you've defined in external
support JS files by using the FFI pattern ``node:support:my_func,my_lib``. This pattern will prompt
idris to look in any ``data`` directories it knows about for a ``js`` folder and a file named
``my_lib.js`` within it. So, you can specify a post-install hook for your package that copies any
needed support JS files into the ``pkgname-<version>/data/js`` folder to enable Idris to later build
that support file into any JS executables that depend on your package.

