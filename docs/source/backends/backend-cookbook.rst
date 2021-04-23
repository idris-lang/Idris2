Custom backend cookbook
=======================

This document addresses the details on how to implement a custom code generation
backend for the Idris compiler.

This part has no insights about how to implement the dependently typed bits.
For that part of the compiler Edwin Brady gave lectures at SPLV20_ which are
available online.

The architecture of the Idris2 compiler makes it easy to implement a custom code
generation back-end.

The way to extend Idris with new back-ends is to use it as a library.
The module ``Idris.Driver`` exports the function ``mainWithCodegens``,
that takes a list of ``(String, Codegen)``, starting idris with these codegens
in addition to the built-in ones.
The first codegen in the list will be set as the default codegen.

Anyone who is interested in implementing a custom back-end needs to answer the
following questions:

- Which Intermediate Representation (IR) should be consumed by the custom back-end?
- How to represent primitive values defined by the ``Core.TT.Constant`` type?
- How to represent Algebraic Data Types?
- How to implement special values?
- How to implement primitive operations?
- How to compile IR expressions?
- How to compile Definitions?
- How to implement Foreign Function Interface?
- How to compile modules?
- How to embed code snippets?
- What should the runtime system support?

First of all, we should know that Idris2 is not an optimizing compiler.
Currently its focus is only to compile dependently typed functional code
in a timely manner.
Its main purpose is to check if the given program is correct in a dependently
typed setting and generate code in form of a lambda-calculus like IR where
higher-order functions are present.
Idris has 3 intermediate representations for code generation.
At every level we get a simpler representation, closer to machine code, but it
should be stressed that all the aggressive code optimizations should happen in
the custom back-ends.
The quality and readability of the generated back-end code is on the shoulders
of the implementor of the back-end. Idris erases type information, in the IRs as
it compiles to scheme by default, and there is no need to keep the type
information around.
With this in mind let's answer the questions above.

The architecture of an Idris back-end
-------------------------------------

Idris compiles its dependently typed front-end language into a representation
which is called ``Compile.TT.Term`` .
This data type has a few constructors and it represents a dependently typed
term.
This ``Term`` is transformed to ``Core.CompileExpr.CExp`` which has more
constructors than ``Term`` and it is a very similar construct to a lambda
calculus with let bindings, structured and tagged data representation,
primitive operations, external operations, and case expressions.
The ``CExp`` is closer in the compiling process to code generation.

The custom code generation back-end gets
a context of definitions,
a template directory and an an output directory,
a ``Core.TT.ClosedTerm`` to compile and a path to an output file.

.. code-block:: idris

   compile : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String)
           -> ClosedTerm -> (outfile : String) -> Core (Maybe String)
   compile defs tmpDir outputDir term file = ?

The ``ClosedTerm`` is a special ``Term`` where the list of the unbound
variables is empty.
This technicality is not important for the code generation of the custom
back-end as the back-end needs to call the ``getCompileData`` function
which produces the ``Compiler.Common.CompileData`` record.

The ``CompileData`` contains:

- A main expression that will be the entry point for the program in ``CExp``
- A list of ``Core.CompileExpr.NamedDef``
- A list of lambda-lifted definitions ``Compiler.LambdaLift.LiftedDef``
- A list of ``Compiler.ANF.ANFDef``
- A list of ``Compiler.VMCode.VMDef`` definitions

These lists contain:

- Functions
- Top-level data definitions
- Runtime crashes which represent unfilled holes,
  explicit calls by the user to ``idris_crash``,
  and unreachable branches in case trees
- Foreign call constructs

The job of the custom code generation back-end is to transform one of the phase
encoded definitions (``NamedDef``, ``LiftedDef``, ``CExp``, ``ANF``, or ``VM``)
into the intermediate representation of the code generator.
It can then run optimizations and generate some form of executable.
In summary, the code generator has to understand how to represent tagged data
and function applications (even if the function application is partial), how
to handle let expressions, how to implement and invoke primitive operations,
how to handle ``Erased`` arguments, and how to do runtime crashes.

The implementor of the custom back-end should pick the closest Idris IR which
fits to the abstraction of the technology that is aimed to compile to.
The implementor should also consider how to transform the simple main expression
which is represented in CExp.
As Idris does not focus on memory management and threading. The custom back-end
should model these concepts for the program that is compiled.
One possible approach is to target a fairly high level language and reuse as
much as possible from it for the custom back-end.
Another possibility is to implement a runtime that is capable of handling memory
management and threading.

Which Intermediate Representation (IR) should be consumed by the custom back-end?
---------------------------------------------------------------------------------

Now lets turn our attention to the different intermediate representations (IRs)
that Idris provides.
When the ``getCompiledData`` function is invoked with the ``Phase`` parameter
it will produce a ``CompileData`` record, which will contain lists of top-level
definitions that needs to be compiled. These are:

- ``NamedDef``
- ``LiftedDef``
- ``ANFDef``
- ``VMDef``

The question to answer here is: Which one should be picked?
Which one fits to the custom back-end?

How to represent primitive values defined by the ``Core.TT.Constant`` type?
---------------------------------------------------------------------------

After one selects the IR to be used during code generation, the next question
to answer is how primitive types should be represented in the back-end.
Idris has the following primitive types:

- ``Int``
- ``Integer`` (arbitrary precision)
- ``Bits(8/16/32/64)``
- ``Char``
- ``String``
- ``Double``
- ``WorldVal`` (token for IO computations)

And as Idris allows pattern matching on types all the primitive types have
their primitive counterpart for describing a type:

- ``IntType``
- ``IntegerType``
- ``Bits(8/16/32/64)Type``
- ``StringType``
- ``CharType``
- ``DoubleType``
- ``WorldType``

The representation of these primitive types should be a well-thought out
design decision as it affects many parts of the code generation, such as
conversion from the back-end values when FFI is involved, big part of the
data during the runtime is represented in these forms.
Representation of primitive types affect the possible optimisation techniques,
and they also affect the memory management and garbage collection.

There are two special primitive types: String and World.

**String**

As its name suggest this type represent a string of characters. As mentioned in
`Primitive FFI Types <https://idris2.readthedocs.io/en/latest/ffi/ffi.html#primitive-ffi-types>`_,
Strings are encoded in UTF-8.

It is not always clear who is responsible for freeing up a ``String`` created by
a component other than the Idris runtime. Strings created in Idris will
always have value, unlike possible String representation of the host technology,
where for example NULL pointer can be a value, which can not happen on the Idris side.
This creates constraints on the possible representations of the Strings in the
custom back-end and diverging from the Idris representation is not a good idea.
The best approach here is to build a conversion layer between the string
representation of the custom back-end and the runtime.

**World**

In pure functional programming, causality needs to be represented whenever we
want to maintain the order in which subexpressions are executed.
In Idris a token is used to chain IO function calls.
This is an abstract notion about the state of the world. For example this
information could be the information that the runtime needs for bookkeeping
of the running program.

The ``WorldVal`` value in Idris programs is accessed via the ``primIO``
construction which leads us to the ``PrimIO`` module.
Let's see the relevant snippets:

.. code-block:: idris

   data IORes : Type -> Type where
        MkIORes : (result : a) -> (1 x : %World) -> IORes a

   fromPrim : (1 fn : (1 x : %World) -> IORes a) -> IO a
   fromPrim op = MkIO op

   primIO : HasIO io => (1 fn : (1 x : %World) -> IORes a) -> io a
   primIO op = liftIO (fromPrim op)

The world value is referenced as ``%World`` in Idris.
It is created by the runtime when the program starts.
Its content is changed by the custom runtime.
More precisely, the World is created when the ``WorldVal`` is evaluated during
the execution of the program.
This can happen when the program gets initialized or when an ``unsafePerformIO``
function is executed.

How to represent Algebraic Data Types?
--------------------------------------

In Idris there are two different ways to define a data type: tagged unions are
introduced using the ``data`` keyword while structs are declared via the
``record`` keyword.
Declaring a ``record`` amounts to defining a named collection of fields.
Let's see examples for both:

.. code-block:: idris

   data Either a b
     = Left  a
     | Right b

.. code-block:: idris

   record Pair a b
     constructor MkPair
     fst : a
     snd : b

Idris offers not only algebraic data types but also indexed families. These
are tagged union where different constructors may have different return types.
Here is ``Vect`` an example of a data type which is an indexed family
corresponding to a linked-list whose length is known at compile time.
It has one index (of type ``Nat``) representing the length of the list (the
value of this index is therefore different for the ``[]`` and ``(::)``
constructors) and a parameter (of type ``Type``) corresponding to the type
of values stored in the list.

.. code-block:: idris

   data Vect : (size : Nat) -> Type -> Type where
     Nil  : Vect 0 a                         -- empty list: size is 0
     (::) : a -> Vect n a -> Vect (1 + n) a  -- extending a list of size n: size is 1+n

Both data and record are compiled to constructors in the intermediate
representations. Two examples of such Constructors are
``Core.CompileExpr.CExp.CCon`` and ``Core.CompileExpr.CDef.MkCon``.

Compiling the ``Either`` data type will produce three constructor definitions
in the IR:

- One for the ``Either`` type itself, with the arity of two.
  Arity tells how many parameters of the constructor should have.
  Two is reasonable in this case as the original Idris ``Either`` type has
  two parameters.
- One for the ``Left`` constructor with arity of three.
  Three may be surprising, as the constructor only has one argument in Idris,
  but we should keep in mind the type parameters for the data type too.
- One for the ``Right`` constructor with arity of three.

In the IR constructors have unique names. For efficiency reasons,
Idris assigns a unique integer tag to each data constructors so that constructor
matching is reduced to comparisons of integers instead of strings.
In the ``Either`` example above ``Left`` gets tag 0 and ``Right`` gets tag 1.

Constructors can be considered structured information: a name
together with parameters.
The custom back-end needs to decide how to represent such data.
For example using ``Dict`` in Python, ``JSON`` in JavaScript, etc.
The most important aspect to consider is that these structured values
are heap related values, which should be created and stored dynamically.
If there is an easy way to map in the host technology, the memory management
for these values could be inherited. If not, then the host technology is
responsible for implementing an appropriate memory management.
For example ``RefC`` is a C backend that implements its own memory management
based on reference counting.

How to implement special values?
--------------------------------

Apart from the data constructors there are two special kind of values present
in the Idris IRs: type constructors and ``Erased``.

Type constructors
~~~~~~~~~~~~~~~~~

Type and data constructors that are not relevant for the program's runtime
behaviour may be used at compile butand will be erased from the intermediate
representation.

However some type constructors need to be kept around even at runtime
because pattern matching on types is allowed in Idris:

.. code-block:: idris

   notId : {a : Type} -> a -> a
   notId {a=Int} x = x + 1
   notId x = x

Here we can pattern match on ``a`` and ensure that ``notId`` behaves differently
on ``Int`` than all the other types.
This will generate an IR that will contain a ``Case`` expression with two
branches:
one ``Alt`` matching on the ``Int`` type constructor
and a default for the non-``Int`` matching part of the ``notId`` function.

This is not that special: ``Type`` is a bit like an infinite data type that
contains all of the types a user may ever declare or use.
This can be handled in the back-end and host language using the same mechanisms
that were mobilised to deal with data constructors.
The reason for using the same approach is that in dependently typed languages,
the same language is used to form both type and value level expressions.
Compilation of type level terms will be the same as that of value level terms.
This is one of the things that make dependently typed abstraction elegant.

``Erased``
~~~~~~~~~~

The other kind of special value is ``Erased``.
This is generated by the Idris compiler and part of the IR if the original value
is only needed during the type elaboration process. For example:

.. code-block:: idris

   data Subset : (type : Type)
              -> (pred : type -> Type)
              -> Type
     where
       Element : (value : type)
              -> (0 prf : pred value)
              -> Subset type pred

Because ``prf`` has quantity ``0``, it is guaranteed to be erased during
compilation and thus not present at runtime.
Therefore ``prf`` will be represented as ``Erased`` in the IR.
The custom back-end needs to represent this value too as any other data value,
as it could occur in place of normal values.
The simplest approach is to implement it as a special data constructor and let
the host technology provided optimizations take care of its removal.

How to implement primitive operations?
--------------------------------------

Primitive operations are defined in the module ``Core.TT.PrimFn``.
The constructors of this data type represent the primitive operations that
the custom back-end needs to implement.
These primitive operations can be grouped as:

- Arithmetic operations (``Add``, ``Sub``, ``Mul``, ``Div``, ``Mod``, ``Neg``)
- Bit operations (``ShiftL``, ``ShiftR``, ``BAnd``, ``BOr``, ``BXor``)
- Comparison operations (``LT``, ``LTE``, ``EQ``, ``GTE``, ``GT``)
- String operations
  (``Length``, ``Head``, ``Tail``, ``Index``, ``Cons``, ``Append``,
  ``Reverse``, ``Substr``)
- Double precision floating point operations
  (``Exp``, ``Log``, ``Sin``, ``Cos``, ``Tan``, ``ASin``, ``ACos``, ``ATan``,
  ``Sqrt``, ``Floor``, ``Ceiling``)
- Casting of numeric and string values
- An unsafe  cast operation ``BelieveMe``
- A ``Crash`` operation taking a type and a string and creating a value at that
  type by raising an error.

BelieveMe
~~~~~~~~~

The primitive ``believe_me`` is an unsafe cast that allows users to bypass the
typechecker when they know something to be true even though it cannot be proven.

For instance, assuming that Idris' primitives are correctly implemented, it
should be true that if a boolean equality test on two ``Int`` ``i`` and ``j``
returns ``True`` then ``i`` and ``j`` are equal.
Such a theorem can be implemented by using ``believe_me`` to caset ``Refl``
(the constructor for proofs of a propositional equality) from ``i === i`` to
``i === j``. In this case, it should be safe to implement

Boxing
~~~~~~

Idris assumes that the back-end representation of the data is not strongly typed
and that all the data type have the same kind of representation.
This could introduce a constraint on the representation of the primitives and
constructor represented data types.
One possible solution is that the custom back-end should represent primitive
data types the same way it does constructors, using special tags.
This is called boxing.

Official backends represent primitive data types as boxed ones.
- RefC: Boxes the primitives, which makes them easy to put on the heap.
- Scheme: Prints the values that are a ``Constant`` as Scheme literals.

How to compile top-level definitions?
-------------------------------------

As mentioned earlier, Idris has 4 different IRs that are available in
the ``CompileData`` record: ``Named``, ``LambdaLifted``, ``ANF``, and ``VMDef``.
When assembling the ``CompileData`` we have to tell the Idris compiler which
level we are interested in.
The ``CompileData`` contains lists of definitions that can be considered as top
level definitions that the custom back-end need to generate functions for.

There are four types of top-level definitions that the code generation back-end
needs to support:

- Function
- Constructor
- Foreign call
- Error

**Function** contains a lambda calculus like expression.

**Constructor** represents a data or a type constructor, and it should
be implemented as a function creating the corresponding data structure
in the custom back-end.

A top-level **foreign call** defines an entry point for calling functions
implemented outside the Idris program under compilation.
The Foreign construction contains a list of Strings which are the snippets
defined by the programmer, the type of the arguments and the return type of
the foreign function. The custom back-end should generate a wrapper function.
More on this on the 'How to do do FFI' section.

A top-level **error** definition represents holes in Idris programs, uses of
``idris_crash``, or unreachable branches in a case tree.
Users may want to execute incomplete programs for testing purposes which is
fine as long as we never actually need the value of any of the holes.
Library writers may want to raise an exception if an unrecoverable error has
happened.
Finally, Idris compiles the unreachable branches of a case tree to runtime
error as it is dead code anyway.


How to compile IR expressions?
------------------------------

The custom back-end should decide which intermediate representation
is used as a starting point. The result of the transformation should be
expressions and functions of the host technology.

Definitions in ``ANF`` and ``Lifted`` are represented as a tree like expression,
where control flow is based on the ``Let`` and ``Case`` expressions.

Case expressions
~~~~~~~~~~~~~~~~

There are two types of case expressions,
one for matching and branching on primitive values such as ``Int``,
and the second one is matching and branching on constructor values.
The two types of case expressions will have two different representation for
alternatives of the cases. These are ``ConstCase`` (for matching on constant
values) and ``ConCase`` (for matching on constructors).

Matching on constructors can be implemented as matching on their tags or,
less efficiently, as matching on the name of the constructor. In both cases
a match should bind the values of the constructor's arguments to variables
in the body of the matching branch.
This can be implemented in various ways depending on the host technology:
switch expressions, case with pattern matching, or if-then-else chains.

When pattern matching binds variables, the number of arguments can be different
from the arity of the constructor defined in top-level definitions and in
``GlobalDef``. This is because all the arguments are kept around at typechecking
time, but the code generator for the case tree removes the ones which are marked
as erased. The code generator of the custom back-end also needs to remove the
erased arguments in the constructor implementation.
In ``GlobalDef``, ``eraseArg`` contains this information, which can be used to
extract the number of arguments which needs to be kept around.


Creating values
~~~~~~~~~~~~~~~

Values can be created in two ways.

If the value is a primitive value, it will be handed to the back-end as
a ``PrimVal``. It should be compiled to a constant in the host language
following the  design decisions made in
the 'How to represent primitive values?' section.

If it is a structured value (i.e. a ``Con``) it should be compiled to a function
in the host language which creates a dynamic value. Design decisions made for
'How to represent constructor values?' is going to have effect here.

Function calls
~~~~~~~~~~~~~~

There are four types of function calls:
- Saturated function calls (all the arguments are there)
- Under-applied function calls (some arguments are missing)
- Primitive function calls (necessarily saturated, ``PrimFn`` constructor)
- Foreign Function calls (referred to by its name)

The ``ANF`` and ``Lifted`` intermediate representations support under-applied
function calls (using the ``UnderApp`` constructor in both IR).
The custom back-end needs to support partial application of functions and
creating closures in the host technology.
This is not a problem with back-ends like Scheme where we get the partial
application of a function for free.
But if the host language does not have this tool in its toolbox, the custom
back-end needs to simulate closures.
One possible solution is to manufacture a closure as a special object storing
the function and the values it is currently applied to and wait until all the
necessary arguments have been received before evaluating it.
The same approach is needed if the ``VMCode`` IR was chosen for code generation.

Let bindings
~~~~~~~~~~~~

Both the ``ANF`` and ``Lifted`` intermediate representations have a
``Let`` construct that lets users assign values to local variables.
These two IRs differ in their representation of bound variables.

``Lifted`` is a type family indexed by the ``List Name`` of local variables
in scope. A variable is represented using ``LLocal``, a constructor that
stores a ``Nat`` together with a proof that it points to a valid name in
the local scope.

``ANF`` is a lower level representation where this kind of guarantees are not
present anymore. A local variable is represented using the ``AV`` constructor
which stores an ``AVar`` whose definition we include below.
The ``ALocal`` constructor stores an ``Int`` that corresponds to the ``Nat``
we would have seen in ``Lifted``.
The ``ANull`` constructor refers to an erased variable and its representation
in the host language will depend on the design choices made in
the 'How to represent ``Erased`` values' section.

.. .code-block:: idri
  data AVar : Type where
     ALocal : Int -> AVar
     ANull : AVar

VMDef specificities
~~~~~~~~~~~~~~~~~~~

``VMDef`` is meant to be the closest IR to machine code.
In ``VMDef``, all the definitions have been compiled to instructions for a small
virtual machine with registers and closures.

Instead of ``Let`` expressions, there only are ``ASSIGN`` statements
at this level.

Instead of ``Case`` expressions binding variables when they successfully match
on a data constructor, ``CASE`` picks a branch based on the constructor itself.
An extra operation called ``PROJECT`` is introduced to explicitly extract a
constructor's argument based on their position.

There are no ``App`` or ``UnderApp``. Both are replaced by ``APPLY`` which
applies only one value and creates a closure from the application. For erased
values the operation ``NULL`` assigns an empty/null value for the register.

How to implement the Foreign Function Interface?
------------------------------------------------

The Foreign Function Interface (FFI) plays a big role in running Idris programs.
The primitive operations which are mentioned above are functions for
manipulating values and those functions aren't meant for complex interaction
with the runtime system.
Many of the primitive types can be thought of as abstract types provided via
``external`` and foreign functions to manipulate them.

The responsibility of the custom back-end and the host technology is
to represent these computations the operationally correct way.
The design decisions with respect to representing primitive types in the host
technology will inevitably have effects on the design of the FFI.

Foreign Types
~~~~~~~~~~~~~

Originally Idris had an official back-end implementation in C. Even though
this has changed, the names in the types for the FFI kept their C prefix.
The ``Core.CompileExpr.CFType`` contains the following definitions, many of
them one-to-one mapping from the corresponding primitive type, but some of
them needs explanation.

The foreign types are:

- ``CFUnit``
- ``CFInt``
- ``CFUnsigned(8/16/32/64)``
- ``CFString``
- ``CFDouble``
- ``CFChar``
- ``CFFun`` of type  ``CFType -> CFType -> CFType``
  Callbacks can be registered in the host technology via parameters that have
  CFFun type. The back-end should be able to handle functions that are
  defined in Idris side and compiled to the host technology. If the custom
  back-end supports higher order functions then it should
  be used to implement the support for this kind of FFI type.
- ``CFIORes`` of type ``CFType -> CFType``
  Any ``PrimIO`` defined computation will have this extra layer.
  Pure functions shouldn't have any observable IO effect on the program state
  in the host technology implemented runtime.
  NOTE: ``IORes`` is also used when callback functions are registered in the
  host technology.
- ``CFWorld``
  Represents the current state of the world. This should refer to a token that
  is passed around between function calls.
  The implementation of the World value should contain back-end
  specific values and information about the state of the Idris runtime.
- ``CFStruct`` of type ``String -> List (String, CFType) -> CFType`` is the
  foreign type associated with the ``System.FFI.Struct``.
  It represents a C like structure in the custom back-end.
  ``prim__getField`` and ``prim__setField`` primitives should be implemented
  to support this CFType.
- ``CFUser`` of type ``Name -> List CFType -> CFType``
  Types defined with [external] are represented with ``CFUser``. For example
  ``data MyType : Type where [external]`` will be represented as
  ``CFUser Module.MyType []``
- ``CFBuffer``
  Foreign type defined for ``Data.Buffer``.
  Although this is an external type, Idris builds on a random access buffer.
- ``CFPtr`` The ``Ptr t`` and ``AnyPtr`` are compiled to ``CFPtr``
  Any complex structured data that can not be represented as a simple primitive
  can use this CFPtr to keep track where the value is used.
  In Idris ``Ptr t`` is defined as external type.
- ``CFGCPtr`` The ``GCPtr t`` and ``GCAnyPtr`` are compiled to ``CFGCPtr``.
  ``GCPtr`` is inferred from a Ptr value calling the ``onCollect`` function and
  has a special property. The ``onCollect`` attaches a finalizer for the pointer
  which should run when the pointer is freed.

Examples
~~~~~~~~

Let's step back and look into how this is represented at the Idris source level.
The simplest form of a definition involving the FFI a function definition with
a ``%foreign`` pragma. The pragma is passed a list of strings corresponding to
a mapping from backends to names for the foreign calls. For instance:

.. .code-block:: idris

  %foreign "C:add,libsmallc"
  prim__add : Int -> Int -> Int

this function should be translated by the C back end as a call to the ``add``
function defined in the ``smallc.c`` file. In the FFI, ``Int`` is translated to
``CFInt``. The back-end assumes that the data representation specified in the
library file correspond to that of normal Idris values.

We can also define ``external`` types like in the following examples:

.. .code-block:: idris

  data ThreadID : Type where [external]

  %foreign "scheme:blodwen-thread"
  prim__fork : (1 prog : PrimIO ()) -> PrimIO ThreadID

Here ``ThreadID`` is defined as an external type and this type will be
represented as ``CFUser "ThreadID" []`` internally. The value which is
created by the scheme runtime will be considered as a black box.

The type of ``prim__fork``, once translated as a foreign type, is
``[%World -> IORes Unit, %World] -> IORes Main.ThreadID``
Here we see that the ``%World`` is added to the IO computations.
The ``%World`` parameter is always the last in the argument list.

For the FFI functions, the type information and the user defined string can
be found in the top-level definitions.
The custom back-end should use the definitions to generate wrapper code,
which should convert the types that are described by the ``CFType`` to the
types that the function in the ``%foreign`` directive needs..

How to compile modules?
-----------------------

The Idris compiler generates intermediate files for modules, the content of
the files are neither part of ``Lifted``, ``ANF``, nor ``VMCode``.
Because of this, when the compilation pipeline enters the stage of code
generation, all the information will be in one instance of the ``CompileData``
record and the custom code generator back-end can process them as it would
see the whole program.

The custom back-end has the option to introduce some hierarchy for the functions
in different namespaces and organize some module structure to let the host
technology process the bits and pieces in different sized chunks.
However, this feature is not in the scope of the Idris compiler.

It is worth noting that modules can be mutually recursive in Idris.
So a direct compilation of Idris modules to modules in the host language
may be unsuccessful.

How to embed code snippets?
---------------------------

A possible motivation for implementing a custom back-end for Idris is to
generate code that is meant to be used in a larger project. This project
may be bound to another language that has many useful librarie  but could
benefit from relying on Idris' strong type system in places.

When writing a code generator for this purpose, the interoperability of the
host technology and Idris based on the Foreign Interface can be inconvenient.
In this situation, the need to embed code of the host technology arises
naturally. Elaboration can be an answer for that.

Elaboration is a typechecking time code generation technique.
It relies on the ``Elab`` monad to write scripts that can interact with the
typechecking machinery to generate Idris code in ``Core.TT``.

When code snippets need to be embedded a custom library should be provided
with the custom back-end to turn the valid code snippets into their
representation in ``Core.TT``.

What should the runtime system support?
---------------------------------------

As a summary, a custom back-end for the Idris compiler should create an environment
in the host technology that is able to run Idris programs. As Idris is part of
the family of functional programming languages, its computation model is based
on graph reduction. Programs represented as simple graphs in the memory are based
on the closure creation mechanism during evaluation. Closure creation exist even
on the lowest levels of IRs. For that reason any runtime in
any host technology needs to support some kind of representation of closures
and be able to store them on the heap, thus the responsibility of memory management
falls on the lap of the implementor of the custom back-end. If the host technology
has memory management, the problem is not difficult. It is also likely
that storing closures can be easily implemented via the tools of the host technology.

Although it is not clear how much functionality a back-end should support.
Tools from the Scheme back-end are brought into the Idris world via external types and primitive operations
around them. This is a good practice and gives the community the ability to focus on
the implementation of a quick compiler for a dependently typed language.
One of these hidden features is the concurrency primitives. These are part of the
different libraries that could be part of the compiler or part of the
contribution package. If the threading model is different for the host technology
that the Idris default back-end inherits currently from the Scheme technology it could be a bigger
piece of work.

IO in Idris is implemented using an abstract ``%World`` value, which serves as token for
functions that operate interactively with the World through simple calls to the
underlying runtime system. The entry point of the program is the main function, which
has the type of the IO unit, such as ``main : IO ()``. This means that every
program which runs, starts its part of some IO computation. Under the hood this is
implemented via the creation of the ``%World`` abstract value, and invoking the main
function, which is compiled to pass the abstract %World value for IO related
foreign or external operations.

There is an operation called ``unsafePerformIO`` in the ``PrimIO`` module.
The type signature of ``unsafePerformIO`` tells us that it is capable of
evaluating an ``IO`` computation in a pure context.
Under the hood it is run in exactly the same way the ``main`` function is.
It manufactures a fresh ``%World`` token and passes it to the ``IO`` computations.
This leads to a design decision: How to
represent the state of the World, and how to
represent the world that is instantiated for the sake of the ``unsafePerformIO`` operation via the
``unsafeCreateWorld``? Both the mechanisms of ``main`` and ``unsafeCreateWorld``
use the ``%MkWorld`` constructor, which will be compiled to ``WorldVal`` and
its type to ``WorldType``, which means the implementation of the runtime
is responsible for creating the abstraction around the World. Implementation of an
abstract World value could be based on a singleton pattern, where we can have
just one world, or we could have more than one world, resulting in parallel
universes for ``unsafePerformIO``.

.. _SPLV20: https://www.youtube.com/playlist?list=PLmYPUe8PWHKqBRJfwBr4qga7WIs7r60Ql
.. _Elaboration: https://github.com/stefan-hoeck/idris2-elab-util/blob/main/src/Doc/Index.md
