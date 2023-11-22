**********************
Debugging The Compiler
**********************

Performance
===========

The compiler has the ``--timing`` flag to dump timing information collected during operation.

The output documents, in reverse chronological order, the cumulative time taken for the operation (and sub operations) to complete.
Sub levels are indicated by successive repetitions of ``+``.

.. _sect-logging:

Logging
=======

The compiler logs various categories of information during operation at various levels.

Log levels are characterised by two things:

+ a dot-separated path of ever finer topics of interest e.g. scope.let
+ a natural number corresponding to the verbosity level e.g. 5

If the user asks for some logs by writing::

    %logging "scope" 5

they will get all of the logs whose path starts with `scope` and whose
verbosity level is less or equal to `5`. By combining different logging
directives, users can request information about everything (with a low
level of details) and at the same time focus on a particular subsystem
they want to get a lot of information about. For instance:::

    %logging 1
    %logging "scope.let" 10

will deliver basic information about the various phases the compiler goes
through and deliver a lot of information about scope-checking let binders.


You can set the logging level at the command line using::

    --log <level>

and through the REPL using::

    :log <string category> <level>

    :logging <string category> <level>

The supported logging categories can be found using the command line flag::

    --help logging

REPL Commands
=============

To see more debug information from the REPL there are several options one can set.

.. csv-table:: Logging Categories
   :header: "command", "description"
   :widths: 20, 20

   ``:di <name>``, show debugging information for a name
   ``:set showimplicits``, show values of implicit arguments

Compiler Flags
==============

There are several 'hidden' compiler flags that can help expose Idris' inner workings.

.. csv-table:: Logging Categories
   :header: "command", "description"
   :widths: 20, 20

   ``--dumpcases <file>``, dump case trees to the given file
   ``--dumplifted <file>``, dump lambda lifted trees to the given file
   ``--dumpanf <file>``, dump ANF to the given file
   ``--dumpvmcode <file>``, dump VM Code to the given file
   ``--debug-elab-check``, do more elaborator checks (currently conversion in LinearCheck)


Output Formats
==============

Debug Output
------------

Calling ``:di <name>`` dumps debugging information about the selected term.
Specifically dumped are:

.. csv-table:: Debugging Information
   :header: "topic", "description"
   :widths: 20, 20

   Full Name(s), The fully qualified name of the term.
   Multiplicity, The terms multiplicity.
   Erasable Arguments, Things that are erased.
   Detaggable argument types,
   Specialised arguments,
   Inferrable arguments,
   Compiled version,
   Compile time linked terms,
   Runtime linked terms,
   Flags,
   Size change graph,
