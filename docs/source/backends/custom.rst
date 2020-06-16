**********************************
Building Idris 2 with new backends
**********************************

The way to extend Idris 2 with new backends is to use it as
a library. The module ``Idris.Driver`` exports the function
``mainWithCodegens``, that takes a list of ``(String, Codegen)``,
starting idris with these codegens in addition to the built-in ones.

Getting started
===============

To use Idris 2 as a library you need to install it with (at the top level of the
Idris2 repo)

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
