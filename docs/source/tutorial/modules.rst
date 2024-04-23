.. _sect-namespaces:

**********************
Modules and Namespaces
**********************

An Idris program consists of a collection of modules. Each module
includes an optional ``module`` declaration giving the name of the
module, a list of ``import`` statements giving the other modules which
are to be imported, and a collection of declarations and definitions of
types, interfaces and functions. For example, the listing below gives a
module which defines a binary tree type ``BTree`` (in a file
``BTree.idr``):

.. code-block:: idris

    module BTree

    public export
    data BTree a = Leaf
                 | Node (BTree a) a (BTree a)

    export
    insert : Ord a => a -> BTree a -> BTree a
    insert x Leaf = Node Leaf x Leaf
    insert x (Node l v r) = if (x < v) then (Node (insert x l) v r)
                                       else (Node l v (insert x r))

    export
    toList : BTree a -> List a
    toList Leaf = []
    toList (Node l v r) = BTree.toList l ++ (v :: BTree.toList r)

    export
    toTree : Ord a => List a -> BTree a
    toTree [] = Leaf
    toTree (x :: xs) = insert x (toTree xs)

The modifiers ``export`` and ``public export`` say which names are visible
from other namespaces. These are explained further below.

Then, this gives a main program (in a file
``bmain.idr``) which uses the ``BTree`` module to sort a list:

.. code-block:: idris

    module Main

    import BTree

    main : IO ()
    main = do let t = toTree [1,8,2,7,9,3]
              print (BTree.toList t)

The same names can be defined in multiple modules: names are *qualified* with
the name of the module. The names defined in the ``BTree`` module are, in full:

+ ``BTree.BTree``
+ ``BTree.Leaf``
+ ``BTree.Node``
+ ``BTree.insert``
+ ``BTree.toList``
+ ``BTree.toTree``

If names are otherwise unambiguous, there is no need to give the fully
qualified name. Names can be disambiguated either by giving an explicit
qualification, using the ``with`` keyword, or according to their type.

The ``with`` keyword in expressions comes in two variants:

* ``with BTree.insert (insert x empty)`` for one name
* ``with [BTree.insert, BTree.empty] (insert x empty)`` for multiple names

This is particularly useful with ``do`` notation, where it can often improve
error messages: ``with MyModule.(>>=) do ...``

If a file contains a module declaration ``module Foo.Bar.MyModule``, its
path relative to the ``sourcedir`` specified in the ``.ipkg`` project file
(defaults to ``.``) must be ``./Foo/Bar/MyModule.idr``. If you are not using an
``.ipkg`` project file, the path must be relative to the directory you are
running Idris from. Similarly, an ``import`` statement also refers to such a
relative filepath stripped of its file extension, using dots to separate
directories. As in the example above, all modules names and directories must be
capitalised identifiers. If a file does not contain a module declaration, it
is considered to be a module whose identifier is ``Main``.

Export Modifiers
================

Idris allows for fine-grained control over the visibility of a
namespace's contents. By default, all names defined in a namespace are kept
private.  This aids in specification of a minimal interface and for
internal details to be left hidden. Idris allows for functions,
types, and interfaces to be marked as: ``private``, ``export``, or
``public export``. Their general meaning is as follows:

- ``private`` meaning that it is not exported at all. This is the default.

- ``export`` meaning that its top level type is exported.

- ``public export`` meaning that the entire definition is exported.

A further restriction in modifying the visibility is that definitions must not
refer to anything within a lower level of visibility. For example, ``public
export`` definitions cannot use ``private`` or ``export`` names, and ``export``
types cannot use ``private`` names. This is to prevent private names leaking
into a module's interface.

Meaning for Functions
---------------------

- ``export`` the type is exported

- ``public export`` the type and definition are exported, and the
  definition can be used after it is imported. In other words, the
  definition itself is considered part of the module's interface. The
  long name ``public export`` is intended to make you think twice
  about doing this.

.. note::

   Type synonyms in Idris are created by writing a function. When
   setting the visibility for a module, it is usually a good idea to
   ``public export`` all type synonyms if they are to be used outside
   the module. Otherwise, Idris won't know what the synonym is a
   synonym for.

Since ``public export`` means that a function's definition is exported,
this effectively makes the function definition part of the module's API.
Therefore, it's generally a good idea to avoid using ``public export`` for
functions unless you really mean to export the full definition.

.. note::
    *For beginners*:
    If the function needs to be accessed only at runtime, use ``export``.
    However, if it's also meant to be used at *compile* time (e.g. to prove
    a theorem), use ``public export``.
    For example, consider the function ``plus : Nat -> Nat -> Nat`` discussed
    previously, and the following theorem: ``thm : plus Z m = m``.
    In order to prove it, the type checker needs to reduce ``plus Z m`` to ``m``
    (and hence obtain ``thm : m = m``).
    To achieve this, it will need access to the *definition* of ``plus``,
    which includes the equation ``plus Z m = m``.
    Therefore, in this case, ``plus`` has to be marked as ``public export``.

Meaning for Data Types
----------------------

For data types, the meanings are:

- ``export`` the type constructor is exported

- ``public export`` the type constructor and data constructors are exported


Meaning for Interfaces
----------------------

For interfaces, the meanings are:

- ``export`` the interface name is exported

- ``public export`` the interface name, method names and default
  definitions are exported

Meaning for fixity declarations
-------------------------------

The modifiers differ slightly when applied to fixities. Un-labelled
fixities are exported rather than be private. There is no difference between
`public export` and `export`. In summary:

- ``private`` means the fixity declaration is only visible within the file.

- ``public export`` and ``export`` are the same and the fixity is exported.
  The access modifier could also be eluded for the same effect.

Propagating Inner Module API's
-------------------------------

Additionally, a module can re-export a module it has imported, by using
the ``public`` modifier on an ``import``. For example:

::

    module A

    import B
    import public C

The module ``A`` will export the name ``a``, as well as any public or
abstract names in module ``C``, but will not re-export anything from
module ``B``.

Renaming imports
----------------

Sometimes it is convenient to be able to access the names in another module
via a different namespace (typically, a shorter one). For this, you can
use `import...as`. For example:

::

    module A

    import Data.List as L

This module ``A`` has access to the exported names from module ``Data.List``,
but can also explicitly access them via the module name ``L``. ``import...as``
can also be combined with ``import public`` to create a module which exports
a larger API from other sub-modules:

::

    module Books

    import public Books.Hardback as Books
    import public Books.Comic as Books

Here, any module which imports ``Books`` will have access to the exported
interfaces of ``Books.Hardback`` and ``Books.Comic`` both under the namespace
``Books``.

Explicit Namespaces
===================

Defining a module also defines a namespace implicitly. However,
namespaces can also be given *explicitly*. This is most useful if you
wish to overload names within the same module:

.. code-block:: idris

    module Foo

    namespace X
      export
      test : Int -> Int
      test x = x * 2

    namespace Y
      export
      test : String -> String
      test x = x ++ x

This (admittedly contrived) module defines two functions with fully
qualified names ``Foo.X.test`` and ``Foo.Y.test``, which can be
disambiguated by their types:

::

    *Foo> test 3
    6 : Int
    *Foo> test "foo"
    "foofoo" : String

The export rules, ``public export`` and ``export``, are *per namespace*,
not *per file*, so the two ``test`` definitions above need the ``export``
flag to be visible outside their own namespaces.

Explicit namespaces inside functions
------------------------------------

Explicit namespaces can be defined inside ``where``-blocks of functions.
Unlike other definitions (e.g. ``data`` or ``record``),
such namespace definitions are understood as belonging to the scope of the
function definition itself.

For example, the following code should typecheck.

.. code-block:: idris

    withNSInside : Nat
    withNSInside = g where
      namespace X
        export
        g : Nat
        g = 5

    useNSFromOutside : Nat
    useNSFromOutside = X.g

Notice that if a function that contains namespace definition has parameters,
then definitions inside this namespace will have these parameters too.
This is done because such definitions have access to values of the parameters.

These parameters must be passed explicitly when accessing namespaced definitions
from outside the function where they are declared, and must not be passed when
accessed from the inside.
This behaviour is similar to parameterised blocks described below.
Look at the following example.

.. code-block:: idris

    withNSInside' : String -> Nat
    withNSInside' str = String.length g where
      namespace Y
        export
        g : String
        g = str ++ "a"

    useNSFromOutside' : String
    useNSFromOutside' = Y.g "x" -- value is "xa"

Parameterised blocks
====================

Groups of functions can be parameterised over a number of arguments
using a ``parameters`` declaration, for example:

.. code-block:: idris

    parameters (x : Nat, y : Nat)
      addAll : Nat -> Nat
      addAll z = x + y + z

The effect of a ``parameters`` block is to add the declared parameters
to every function, type and data constructor within the
block. Specifically, adding the parameters to the front of the
argument list. Outside the block, the parameters must be given
explicitly. The ``addAll`` function, when called from the REPL, will
thus have the following type signature.

::

    *params> :t addAll
    addAll : Nat -> Nat -> Nat -> Nat

and the following definition.

.. code-block:: idris

    addAll : (x : Nat) -> (y : Nat) -> (z : Nat) -> Nat
    addAll x y z = x + y + z

Parameters blocks can be nested, and can also include data declarations,
in which case the parameters are added explicitly to all type and data
constructors. They may also be dependent types with implicit arguments:

.. code-block:: idris

    parameters (y : Nat, xs : Vect x a)
      data Vects : Type -> Type where
        MkVects : Vect y a -> Vects a

      append : Vects a -> Vect (x + y) a
      append (MkVects ys) = xs ++ ys

To use ``Vects`` or ``append`` outside the block, we must also give the
``xs`` and ``y`` arguments. Here, we can use placeholders for the values
which can be inferred by the type checker:

::

    Main> show (append _ _ (MkVects _ [1,2,3] [4,5,6]))
    "[1, 2, 3, 4, 5, 6]"
