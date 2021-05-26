**********************
Debugging The Compiler
**********************

Performance
===========

The compiler has the ``--timing`` flag to dump timing information collected during operation.

The output documents, in reverse chronological order, the cumulative time taken for the operation (and sub operations) to complete.
Sub levels are indicated by successive repetitions of ``+``.


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

The supported logging categories are:

.. csv-table:: Logging Categories
   :header: "topic", "description"
   :widths: 20, 20

    ``auto``, some documentation of this option
    ``builtin.Natural``, some documentation of this option
    ``builtin.Natural.addTransform``, some documentation of this option
    ``builtin.NaturalToInteger``, some documentation of this option
    ``builtin.NaturalToInteger.addTransforms``, some documentation of this option
    ``builtin.IntegerToNatural``, some documentation of this option
    ``builtin.IntegerToNatural.addTransforms``, some documentation of this option
    ``compile.casetree``, some documentation of this option
    ``compile.casetree.clauses``, some documentation of this option
    ``compile.casetree.getpmdef``, some documentation of this option
    ``compile.casetree.intermediate``, some documentation of this option
    ``compile.casetree.pick``, some documentation of this option
    ``compile.casetree.partition``, some documentation of this option
    ``compiler.inline.eval``, some documentation of this option
    ``compiler.refc``, some documentation of this option
    ``compiler.refc.cc``, some documentation of this option
    ``compiler.scheme.chez``, some documentation of this option
    ``coverage``, some documentation of this option
    ``coverage.empty``, some documentation of this option
    ``coverage.missing``, some documentation of this option
    ``coverage.recover``, some documentation of this option
    ``declare.data``, some documentation of this option
    ``declare.data.constructor``, some documentation of this option
    ``declare.data.parameters``, some documentation of this option
    ``declare.def``, some documentation of this option
    ``declare.def.clause``, some documentation of this option
    ``declare.def.clause.impossible``, some documentation of this option
    ``declare.def.clause.with``, some documentation of this option
    ``declare.def.impossible``, some documentation of this option
    ``declare.def.lhs``, some documentation of this option
    ``declare.def.lhs.implicits``, some documentation of this option
    ``declare.param``, some documentation of this option
    ``declare.record``, some documentation of this option
    ``declare.record.field``, some documentation of this option
    ``declare.record.projection``, some documentation of this option
    ``declare.record.projection.prefix``, some documentation of this option
    ``declare.type``, some documentation of this option
    ``desugar.idiom``, some documentation of this option
    ``doc.record``, some documentation of this option
    ``elab``, some documentation of this option
    ``elab.ambiguous``, some documentation of this option
    ``elab.app.lhs``, some documentation of this option
    ``elab.as``, some documentation of this option
    ``elab.bindnames``, some documentation of this option
    ``elab.binder``, some documentation of this option
    ``elab.case``, some documentation of this option
    ``elab.def.local``, some documentation of this option
    ``elab.delay``, some documentation of this option
    ``elab.hole``, some documentation of this option
    ``elab.implicits``, some documentation of this option
    ``elab.implementation``, some documentation of this option
    ``elab.interface``, some documentation of this option
    ``elab.interface.default``, some documentation of this option
    ``elab.local``, some documentation of this option
    ``elab.prun``, some documentation of this option
    ``elab.prune``, some documentation of this option
    ``elab.record``, some documentation of this option
    ``elab.retry``, some documentation of this option
    ``elab.rewrite``, some documentation of this option
    ``elab.unify``, some documentation of this option
    ``elab.update``, some documentation of this option
    ``elab.with``, some documentation of this option
    ``eval.casetree``, some documentation of this option
    ``eval.casetree.stuck``, some documentation of this option
    ``eval.eta``, some documentation of this option
    ``eval.stuck``, some documentation of this option
    ``idemode.hole``, some documentation of this option
    ``ide-mode.highlight``, some documentation of this option
    ``ide-mode.highlight.alias``, some documentation of this option
    ``ide-mode.send``, some documentation of this option
    ``import``, some documentation of this option
    ``import.file``, some documentation of this option
    ``interaction.casesplit``, some documentation of this option
    ``interaction.generate``, some documentation of this option
    ``interaction.search``, some documentation of this option
    ``metadata.names``, some documentation of this option
    ``module.hash``, some documentation of this option
    ``quantity``, some documentation of this option
    ``quantity.hole``, some documentation of this option
    ``quantity.hole.update``, some documentation of this option
    ``repl.eval``, some documentation of this option
    ``specialise``, some documentation of this option
    ``totality``, some documentation of this option
    ``totality.positivity``, some documentation of this option
    ``totality.termination``, some documentation of this option
    ``totality.termination.calc``, some documentation of this option
    ``totality.termination.guarded``, some documentation of this option
    ``totality.termination.sizechange``, some documentation of this option
    ``totality.termination.sizechange.checkCall``, some documentation of this option
    ``totality.termination.sizechange.checkCall.inPath``, some documentation of this option
    ``totality.termination.sizechange.checkCall.inPathNot.restart``, some documentation of this option
    ``totality.termination.sizechange.checkCall.inPathNot.return``, some documentation of this option
    ``totality.termination.sizechange.inPath``, some documentation of this option
    ``totality.termination.sizechange.isTerminating``, some documentation of this option
    ``totality.termination.sizechange.needsChecking``, some documentation of this option
    ``transform.lhs``, some documentation of this option
    ``transform.rhs``, some documentation of this option
    ``ttc.read``, some documentation of this option
    ``ttc.write``, some documentation of this option
    ``typesearch.equiv``, some documentation of this option
    ``unelab.case``, some documentation of this option
    ``unify``, some documentation of this option
    ``unify.application``, some documentation of this option
    ``unify.binder``, some documentation of this option
    ``unify.constant``, some documentation of this option
    ``unify.constraint``, some documentation of this option
    ``unify.delay``, some documentation of this option
    ``unify.equal``, some documentation of this option
    ``unify.head``, some documentation of this option
    ``unify.hole``, some documentation of this option
    ``unify.instantiate``, some documentation of this option
    ``unify.invertible``, some documentation of this option
    ``unify.meta``, some documentation of this option
    ``unify.noeta``, some documentation of this option
    ``unify.postpone``, some documentation of this option
    ``unify.retry``, some documentation of this option
    ``unify.search``, some documentation of this option
    ``unify.unsolved``, some documentation of this option

REPL Commands
=============

To see more debug information from the REPL there are several options one can set.

.. csv-table:: Logging Categories
   :header: "command", "description"
   :widths: 20, 20

   ``:di <name>``, show debugging information for a name

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
