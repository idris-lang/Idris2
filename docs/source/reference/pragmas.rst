********
Pragmas
********

.. role:: idris(code)
    :language: idris

Idris2 supports a number of pragmas (identifiable by the `%` prefix). Some pragmas change compiler behavior
until the behavior is changed back using the same pragma while others apply to the following declaration. A
small niche of pragmas apply directly to one or more arguments instead of the code following the pragma
(like the `%name` pragma described below).

.. note::
    This page is a work in progress. If you know about a pragma that is not described yet, please consider
    submitting a pull request!

Global pragmas
====================

``%language``
--------------------

Enable language extensions.  Currently, the only extension is [#ElabReflection]_.

.. code-block:: idris

   %language ElabReflection

``%default``
--------------------

Set the default totality requirement for functions, which can be one of ``total``,
``covering``, or ``partial``.  The value is initially set to ``covering`` unless the ``--total``
command line switch is used, which sets it to ``total``.

``%builtin``
--------------------

The ``%builtin Natural`` pragma converts recursive/unary representations of natural numbers
into primitive ``Integer`` representations.

This pragma is explained in detail on its own page. For more, see :ref:`builtins`.


``%name``
--------------------

Give the compiler some suggested names to use for a particular type when it is asked to generate names for values.
You can specify any number of suggested names; they will be used in-order when more than one is needed for a single
definition.

.. code-block:: idris

   data Foo = X | Y

   %name Foo foo,bar


``%ambiguity_depth``
--------------------

Set how deep nested ambiguous names can be before Idris gives up. The default is 3, increashing this
will effect compiler performance. For more details, see :ref:`ambiguous-name-resolution`.

``%auto_implicit_depth``
------------------------

Set the search depth for ``auto`` implicits. The default value is 50.

``%logging``
--------------------

 Change the logging level.  See :ref:`sect-logging` for details.

 .. code-block:: idris

    %logging 1
    %logging "elab" 5


``%prefix_record_projections``
------------------------------

Configure whether projection functions without a leading period are generated for records. It defaults
to ``on``.  See :ref:`record-elaboration` for more details.

.. code-block:
   %prefix_record_projections on

``%transform``
--------------------

Replace a function at runtime with another implementation. It allows us to
functions that are appropriate for type checking and have an efficient version at runtime. For example:

.. code-block:: idris

    plus : Nat -> Nat -> Nat
    plus Z y = y
    plus (S x) y = S $ plus x y

    %transform "plus" plus j k = integerToNat (natToInteger j + natToInteger j)

``%unbound_implicits``
----------------------

Configure whether implicit bindings are automatically added to function types for unbound
lowercase names. It is on by default. See :ref:`unbound-implicits` for more details.

``%auto_lazy``
--------------------

Configure whether the compiler automatically adds ``delay`` and ``force`` when
necessary.  It defaults to ``on``.


``%search_timeout``
--------------------

Set the expression search timeout in milliseconds.  The default is 1000.

.. code-block:: idris

   %search_timeout 1000


``%nf_metavar_threshold``
-------------------------

Set the maximum number of stuck applications allowed while unifying a meta. The
default value is 25.

``%cg``
--------------------

Codegen directives can be included in source code with the ``%cg`` pragma. For example, instead of
using ``--directive extraRuntime=mycode.ss`` on the command line for the chez backend, you can write:

.. code-block:: idris

    %cg chez extraRuntime=mycode.ss

The ``%cg`` pragma is followed by the name of a codegen and a directive for that codegen, terminated by
newline.  Directives from imported modules, including transitive imports, will aggregate. All of the
directives given in the source are stored in the module, but only the directives for the current codegen
are used at link time.

How directives are treated in aggregate depends on the codegen and directive. For example, the
``extraRuntime`` directive for the Chez codegen is deduplicated.  And the javascript backend gives
the ``minimal`` directive priority over the ``compact`` directive if both are present.

See the section for each codegen under :ref:`sect-execs` for available directives.

Pragmas on declarations
=======================

``%deprecate``
--------------------

Mark the following definition as deprecated. Whenever the function is used, Idris will show a deprecation
warning.

.. code-block:: idris

   %deprecate
   foo : String -> String
   foo x = x ++ "!"

   bar : String
   bar = foo "hello"

.. code-block:: none

   Warning: Deprecation warning: Man.foo is deprecated and will be removed in a future version.

You can use code documentation (triple vertical bar `||| docs`) to suggest a strategy for removing the
deprecated function call and that documentation will be displayed alongside the warning.

.. code-block:: idris

   ||| Please use the @altFoo@ function from now on.
   %deprecate
   foo : String -> String
   foo x = x ++ "!"

   bar : String
   bar = foo "hello"

.. code-block:: none

   Warning: Deprecation warning: Man.foo is deprecated and will be removed in a future version.
     Please use the @altFoo@ function from now on.

``%inline``
--------------------

Instruct the compiler to inline the following definition when it is applied. It is generally best to let the
compiler and the backend you are using optimise code based on its predetermined rules, but if you want to
force a function to be inlined when it is called, this pragma will force it.

.. code-block:: idris

   %inline
   foo : String -> String
   foo x = x ++ "!"

``%noinline``
--------------------

Instruct the compiler _not_ to inline the following definition when it is applied. It is generally best to let the
compiler and the backend you are using optimise code based on its predetermined rules, but if you want to
force a function to never be inlined when it is called, this pragma will force it.

.. code-block:: idris

   %noinline
   foo : String -> String
   foo x = x ++ "!"

``%tcinline``
--------------------

Instruct the compiler to inline the function during totality checking.

``%hide``
--------------------

Hide a definition from imports. This is particularly useful when you are re-definiing functions or types from
a module but still need to import it.

.. code-block:: idris

   module MyNat

   %hide Prelude.Nat
   %hide Prelude.S
   %hide Prelude.Nat

   data Nat = Z | S Nat

You can also hide fixity declarations if you need to redefine your own.

.. code-block:: idris

   module MyNat

   %hide Prelude.Ops.infixl.(+)

   infixr 5 +


``%unhide``
--------------------

The ``%unhide`` pragma unhides a definition that was previously hidden with ``%hide``.


``%unsafe``
--------------------

Mark a function like ``believe_me`` as being unsafe. The function will be semantically
highlighted in a different color to draw the user's attention to its use.


``%spec``
--------------------

Specialise a function according to a list of arguments.

.. code-block:: idris

   %spec a
   identity : List a -> List a
   identity [] = []
   identity (x :: xs) = x :: identity xs


``%foreign``
--------------------

Declare a foreign function.  It is followed by an indented block of expressions
that evaluate to strings. See :ref:`ffi-overview` for more details.


``%foreign_impl``
--------------------

Adds an implementation to an existing ``%foreign`` in another file. This pragma can
be used to fill in an implementation for another backend without changing the original
file. In the case of multiple declarations for a given backend, the backend will choose
the one from the most recently loaded module.

.. code-block:: idris

   %foreign_impl Prelude.IO.prim__fork "javascript:lambda:(proc) => { throw new Error() }"


``%export``
--------------------

Export an Idris function to the underlying host language. The the name for each backend is
given in an indented block of string expressions, similar to ``%foreign``.  Currently this
pragma is only supported by the javascript backend.

.. code-block:: idris

   %export "javascript:addNat"
   addNat : Nat -> Nat -> Nat
   addNat a b = a + b


``%nomangle``
--------------------

This pragma is deprecated.  Instead use ``%export`` to expose functions to the backend.


``%hint``
--------------------

Mark a function to be used for ``auto`` search (see :ref:`auto-implicits` and
:ref:`auto-implicit-arguments` for more).  Hints are used internally for instance
resolution and non-named instances are automatically tagged with ``%hint``.


``%defaulthint``
--------------------

Mark a hint to be tried when no other hints match.

``%globalhint``
--------------------

A global hint is like a ``%hint``, but it is always tried, while ``%hint`` is only tried if the return
type matches.

``%extern``
--------------------

Declare a function to be externally implemented, but relies on codegen
to fill in the function rather than specifying the name. The function name must be explicitly
handled in the codegen. It is used for functions like ``prim__newIORef`` in the prelude.


``%macro``
--------------------

Mark a function that returns the ``Elab`` monad as a macro. When the function is used in
an expression, it will be run at compile time and the invocation will be replaced by the
result of the elaboration.

``%start``
--------------------

The ``%start`` pragma is not implemented.

``%allow_overloads``
--------------------

This pragma is no longer used by the compiler.

Internal
========

These pragmas are used in the prelude, but aren't typically used in user programs.


``%rewrite``
--------------------

Specify the `Equal` type and rewrite function used by rewrite statements.

.. code-block:: idris

   %rewrite Equal rewrite__impl

``%pair``
--------------------

This directive is used in the prelude to tell auto implicit search what to use to look inside pairs.

.. code-block:: idris

   %pair Pair fst snd

``%integerLit``
--------------------

Define the function used to interpret literal integers. In the prelude, it is set
to ``fromInteger``, so a literal ``2`` is elaborated to ``fromInteger 2``.

.. code-block:: idris

   %integerLit fromInteger

``%stringLit``
--------------------

Define the function used to interpret literal strings. In the prelude, it is set
to ``fromString``, so a literal ``"idris"`` is elaborated to ``fromString "idris"``.

.. code-block:: idris

   %stringLit fromString


``%charLit``
--------------------

Define the function used to interpret literal characters. In the prelude, it is set
to ``fromChar``, so a literal ```x```` is elaborated to ``fromChar 'x'``.

.. code-block:: idris

   %charLit fromChar

``%doubleLit``
--------------------

Define the function used to interpret literal numbers with a decimal in them. In the prelude, it is set
to ``fromDouble``, so a literal ```2.0```` is elaborated to ``fromDouble 2.0``.

.. code-block:: idris

   %charLit fromDouble


Reflection Literals
===================


``%TTImpLit``
--------------------

Allow quoted expressions to be cast to a user defined type.

.. code-block:: idris

   %TTImpLit fromTTImp

   public export
   data NatExpr : Type where
        Plus : NatExpr -> NatExpr -> NatExpr
        Mult : NatExpr -> NatExpr -> NatExpr
        Val : Nat -> NatExpr
        Var : String -> NatExpr

   public export
   natExpr : TTImp -> Elab NatExpr
   natExpr `(~(l) + ~(r)) = [| Plus (natExpr l) (natExpr r) |]
   natExpr `(~(l) * ~(r)) = [| Mult (natExpr l) (natExpr r) |]
   natExpr `(fromInteger ~(IPrimVal _ (BI n))) = pure $ Val $ fromInteger n
   natExpr (IVar _ (UN (Basic nm))) = pure $ Var nm
   natExpr s = failAt (getFC s) "Invalid NatExpr"

   %macro
   fromTTImp : TTImp -> Elab NatExpr
   fromTTImp = natExpr

   export
   natExprMacroTest : NatExpr
   natExprMacroTest = `(1 + 2 + x)

``%declsLit``
--------------------

Allow quoted declarations to be cast to user defined types.

``%nameLit``
--------------------

Allow quoted names to be cast to user defined types.


Expressions
===========

Pragmas that occur inside expressions.

``%runElab``
--------------------

The ``%runElab`` pragma can be used at the top level or as an expression. It takes an elaborator
script as an argument which runs in the ``Elab`` monad, has access to Idris' type-checking machinery,
and can generate code.

``%search``
--------------------

Ask Idris to fill in the value with auto-implicit search. See :ref:`auto-implicits` for more details.

``%World``
--------------------

The type of the world token used for IO.  For more information, see :ref:`World<sect-world>`.

``%MkWorld``
--------------------

The world token used for IO.  For more information, see :ref:`World<sect-world>`.

``%syntactic``
--------------------

The ``%syntactic`` pragma can appear after the ``with`` keyword.  It abstracts
over the value syntactically, rather than by value, and can significantly speed
up elaboration where large types are involved, at a cost of being less general.
Try it if "with" is slow.

.. [#ElabReflection] https://github.com/stefan-hoeck/idris2-elab-util/blob/main/src/Doc/Index.md
