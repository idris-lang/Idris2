.. _sect-packages:

********
Packages
********

Idris includes a simple build system for building packages and executables
from a named package description file. These files can be used with the
Idris compiler to manage the development process.

Package Descriptions
====================

A package description includes the following:

+ A header, consisting of the keyword ``package`` followed by a package
  name. Package names can be any valid Idris identifier. The iPKG
  format also takes a quoted version that accepts any valid filename.

+ Fields describing package contents, ``<field> = <value>``.

At least one field must be the modules field, where the value is a
comma separated list of modules. For example, given an idris package
``maths`` that has modules ``Maths.idr``, ``Maths.NumOps.idr``,
``Maths.BinOps.idr``, and ``Maths.HexOps.idr``, the corresponding
package file would be:

::

    package maths

    modules = Maths
            , Maths.NumOps
            , Maths.BinOps
            , Maths.HexOps


Other examples of package files can be found in the ``libs`` directory
of the main Idris repository, and in `third-party libraries
<https://github.com/idris-lang/Idris-dev/wiki/Libraries>`_.


Using Package files
===================

Idris itself is aware about packages, and special commands are
available to help with, for example, building packages, installing
packages, and cleaning packages.  For instance, given the ``maths``
package from earlier we can use Idris as follows:

+ ``idris2 --build maths.ipkg`` will build all modules in the package

+ ``idris2 --install maths.ipkg`` will install the package, making it
  accessible by other Idris libraries and programs.

+ ``idris2 --clean maths.ipkg`` will delete all intermediate code and
  executable files generated when building.

Once the maths package has been installed, the command line option
``--package maths`` makes it accessible (abbreviated to ``-p maths``).
For example:

::

    idris2 -p maths Main.idr

Package Dependencies Using Atom
===============================

If you are using the Atom editor and have a dependency on another package,
corresponding to for instance ``import Lightyear`` or ``import Pruviloj``,
you need to let Atom know that it should be loaded. The easiest way to
accomplish that is with a .ipkg file. The general contents of an ipkg file
will be described in the next section of the tutorial, but for now here is
a simple recipe for this trivial case:

- Create a folder myProject.

- Add a file myProject.ipkg containing just a couple of lines:

.. code-block:: idris

    package myProject

    pkgs = pruviloj, lightyear

- In Atom, use the File menu to Open Folder myProject.
