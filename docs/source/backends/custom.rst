**********************************
Building Idris 2 with new backends
**********************************

The way to extend Idris 2 with new backends is to use it as
a library. The module ``Idris.Driver`` exports the function
``mainWithCodegens``, that takes a list of ``(String, Codegen)``,
starting idris with these codegens in addition to the built-in ones. The first
codegen in the list will be set as the default codegen.

Getting started
===============

To use Idris 2 as a library you need a self-hosting installation and
then install the `idris2api` library (at the top level of the Idris2 repo)

::

    make install-api

Now create a file containing

.. code-block:: idris

    module Main

    import Core.Context
    import Compiler.Common
    import Idris.Driver

    compile : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
            ClosedTerm -> (outfile : String) -> Core (Maybe String)
    compile defs tmpDir outputDir term file = do coreLift $ putStrLn "I'd rather not."
                                                 pure $ Nothing

    execute : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
    execute defs tmpDir term = do coreLift $ putStrLn "Maybe in an hour."

    lazyCodegen : Codegen
    lazyCodegen = MkCG compile execute

    main : IO ()
    main = mainWithCodegens [("lazy", lazyCodegen)]

Build it with

::

    $ idris2 -p idris2 -p contrib -p network Lazy.idr -o lazy-idris2

Now you have an idris2 with an added backend.

::

    $ ./build/exec/lazy-idris2
         ____    __     _         ___
        /  _/___/ /____(_)____   |__ \
        / // __  / ___/ / ___/   __/ /     Version 0.2.0-bd9498c00
      _/ // /_/ / /  / (__  )   / __/      https://www.idris-lang.org
     /___/\__,_/_/  /_/____/   /____/      Type :? for help

    Welcome to Idris 2.  Enjoy yourself!
    With codegen for: lazy
    Main>

It will not be overly eager to actually compile any code with the new backend though

::

    $ ./build/exec/lazy-idris2 --cg lazy Hello.idr -o hello
    I'd rather not.
    $

About the directories
---------------------

The code generator can assume that both ``tmpDir`` and ``outputDir`` exist. ``tmpDir``
is intended for temporary files, while ``outputDir`` is the location to put the desired
output files. By default, ``tmpDir`` and ``outputDir`` point to the same directory
(``build/exec``). The directories can be set from the package description (See Section
:ref:`ref-sect-packages`) or via command line options (Listed in ``idris2 --help``).
