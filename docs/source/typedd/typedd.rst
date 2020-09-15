.. _typedd-index:

Type Driven Development with Idris: Updates Required
====================================================

The code in the book `Type-Driven Development with Idris
<https://www.manning.com/books/type-driven-development-with-idris>`_ by Edwin
Brady, available from `Manning <https://www.manning.com>`_,  will mostly work
in Idris 2, with some small changes as detailed in this document. The updated
code is also [going to be] part of the test suite (see `tests/typedd-book
<https://github.com/edwinb/Idris2/tree/master/tests/typedd-book>`_ in the Idris
2 source).

If you are new to Idris, and learning from the book, we recommend working
through the first 3-4 chapters with Idris 1, to avoid the need to worry about
the changes described here. After that, refer to this document for any
necessary changes.

Chapter 1
---------

No changes necessary

Chapter 2
---------

The Prelude is smaller than Idris 1, and many functions have been moved to
the base libraries instead. So:

In ``Average.idr``, add:

.. code-block:: idris

    import Data.Strings -- for `words`
    import Data.List -- for `length` on lists

In ``AveMain.idr`` and ``Reverse.idr`` add:

.. code-block:: idris

    import System.REPL -- for 'repl'

Chapter 3
---------

Unbound implicits have multiplicity 0, so we can't match on them at run-time.
Therefore, in ``Matrix.idr``, we need to change the type of ``createEmpties``
and ``transposeMat`` so that the length of the inner vector is available to
match on:

.. code-block:: idris

    createEmpties : {n : _} -> Vect n (Vect 0 elem)
    transposeMat : {n : _} -> Vect m (Vect n elem) -> Vect n (Vect m elem)

Chapter 4
---------

For the reasons described above:

+ In ``DataStore.idr``, add ``import System.REPL`` and ``import Data.Strings``
+ In ``SumInputs.idr``, add ``import System.REPL``
+ In ``TryIndex.idr``, add an implicit argument:

.. code-block:: idris

    tryIndex : {n : _} -> Integer -> Vect n a -> Maybe a

+ In exercise 5 of 4.2, add an implicit argument:

.. code-block:: idris

    sumEntries : Num a => {n : _} -> (pos : Integer) -> Vect n a -> Vect n a -> Maybe a

Chapter 5
---------

There is no longer a ``Cast`` instance from ``String`` to ``Nat``, because its
behaviour of returing Z if the ``String`` wasn't numeric was thought to be
confusing and potentially error prone. Instead, there is ``stringToNatOrZ`` in
``Data.Strings`` which at least has a clearer name. So:

In ``Loops.idr`` and ``ReadNum.idr`` add ``import Data.Strings`` and change ``cast`` to
``stringToNatOrZ``

In ``ReadNum.idr``, since functions must now be ``covering`` by default, add
a ``partial`` annotation to ``readNumber_v2``.

Chapter 6
---------

In ``DataStore.idr`` and ``DataStoreHoles.idr``, add ``import Data.Strings`` and
``import System.REPL``. Also in ``DataStore.idr``, the ``schema`` argument to
``display`` is required for matching, so change the type to:

.. code-block:: idris

    display : {schema : _} -> SchemaType schema -> String

In ``TypeFuns.idr`` add ``import Data.Strings``

Chapter 7
---------

``Abs`` is now a separate interface from ``Neg``. So, change the type of ``eval``
to include ``Abs`` specifically:

.. code-block:: idris

    eval : (Abs num, Neg num, Integral num) => Expr num -> num

Also, take ``abs`` out of the ``Neg`` implementation for ``Expr`` and add an
implementation of ``Abs`` as follows:

.. code-block:: idris

    Abs ty => Abs (Expr ty) where
        abs = Abs

Chapter 8
---------

In ``AppendVec.idr``, add ``import Data.Nat`` for the ``Nat`` proofs

``cong`` now takes an explicit argument for the function to apply. So, in
``CheckEqMaybe.idr`` change the last case to:

.. code-block:: idris

    checkEqNat (S k) (S j) = case checkEqNat k j of
                                  Nothing => Nothing
                                  Just prf => Just (cong S prf)

A similar change is necessary in ``CheckEqDec.idr``.

In ``ExactLength.idr``, the ``m`` argument to ``exactLength`` is needed at run time,
so change its type to:

.. code-block:: idris

    exactLength : {m : _} ->
                  (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)

A similar change is necessary in ``ExactLengthDec.idr``. Also, ``DecEq`` is no
longer part of the prelude, so add ``import Decidable.Equality``.

In ``ReverseVec.idr``, add ``import Data.Nat`` for the ``Nat`` proofs.

In ``Void.idr``, since functions must now be ``covering`` by default, add
a ``partial`` annotation to ``nohead`` and its helper function ``getHead``.

Chapter 9
---------

+ In ``ElemType.idr``, add ``import Decidable.Equality``

+ In ``Elem.idr``, add ``import Data.Vect.Elem``

In ``Hangman.idr``:

+ Add ``import Data.Strings``, ``import Data.Vect.Elem`` and ``import Decidable.Equality``
+ ``removeElem`` pattern matches on ``n``, so it needs to be written in its
  type:

.. code-block:: idris

    removeElem : {n : _} ->
                 (value : a) -> (xs : Vect (S n) a) ->
                 {auto prf : Elem value xs} ->
                 Vect n a

+ ``letters`` is used by ``processGuess``, because it's passed to ``removeElem``:

.. code-block:: idris

    processGuess : {letters : _} ->
                   (letter : Char) -> WordState (S guesses) (S letters) ->
                   Either (WordState guesses (S letters))
                          (WordState (S guesses) letters)

+ ``guesses`` and ``letters`` are implicit arguments to ``game``, but are used by the
  definition, so add them to its type:

.. code-block:: idris

    game : {guesses : _} -> {letters : _} ->
           WordState (S guesses) (S letters) -> IO Finished

In ``RemoveElem.idr``

+ Add ``import Data.Vect.Elem``
+ ``removeElem`` needs to be updated as above.

Chapter 10
----------

Lots of changes necessary here, at least when constructing views, due to Idris
2 having a better (that is, more precise and correct!) implementation of
unification, and the rules for recursive ``with`` application being tightened up.

In ``MergeSort.idr``, add ``import Data.List``

In ``MergeSortView.idr``, add ``import Data.List``, and make the arguments to the
views explicit:

.. code-block:: idris

    mergeSort : Ord a => List a -> List a
    mergeSort input with (splitRec input)
      mergeSort [] | SplitRecNil = []
      mergeSort [x] | SplitRecOne x = [x]
      mergeSort (lefts ++ rights) | (SplitRecPair lefts rights lrec rrec)
           = merge (mergeSort lefts | lrec)
                   (mergeSort rights | rrec)

In the problem 1 of exercise 10-1, the ``rest`` argument of the data
constructor ``Exact`` of ``TakeN`` must be made explicit.

.. code-block:: idris

    data TakeN : List a -> Type where
      Fewer : TakeN xs
      Exact : (n_xs : List a) -> {rest : _} -> TakeN (n_xs ++ rest)

In ``SnocList.idr``, in ``my_reverse``, the link between ``Snoc rec`` and ``xs ++ [x]``
needs to be made explicit. Idris 1 would happily decide that ``xs`` and ``x`` were
the relevant implicit arguments to ``Snoc`` but this was little more than a guess
based on what would make it type check, whereas Idris 2 is more precise in
what it allows to unify. So, ``x`` and ``xs`` need to be explicit arguments to
``Snoc``:

.. code-block:: idris

    data SnocList : List a -> Type where
         Empty : SnocList []
         Snoc : (x, xs : _) -> (rec : SnocList xs) -> SnocList (xs ++ [x])

Correspondingly, they need to be explicit when matching. For example:

.. code-block:: idris

      my_reverse : List a -> List a
      my_reverse input with (snocList input)
        my_reverse [] | Empty = []
        my_reverse (xs ++ [x]) | (Snoc x xs rec) = x :: my_reverse xs | rec

Similar changes are necessary in ``snocListHelp`` and ``my_reverse_help``. See
tests/typedd-book/chapter10/SnocList.idr for the full details.

Also, in ``snocListHelp``, ``input`` is used at run time so needs to be bound
in the type:

.. code-block:: idris

    snocListHelp : {input : _} ->
                   (snoc : SnocList input) -> (rest : List a) -> SnocList (input +

It's no longer necessary to give ``{input}`` explicitly in the patterns for
``snocListHelp``, although it's harmless to do so.

In ``IsSuffix.idr``, the matching has to be written slightly differently. The
recursive with application in Idris 1 probably shouldn't have allowed this!

.. code-block:: idris

    isSuffix : Eq a => List a -> List a -> Bool
    isSuffix input1 input2 with (snocList input1, snocList input2)
      isSuffix [] input2 | (Empty, s) = True
      isSuffix input1 [] | (s, Empty) = False
      isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec, Snoc ysrec)
         = if x == y
              then isSuffix xs ys | (xsrec, ysrec)
              else False

This doesn't yet get past the totality checker, however, because it doesn't
know about looking inside pairs.

In ``DataStore.idr``: Well this is embarrassing - I've no idea how Idris 1 lets
this through! I think perhaps it's too "helpful" when solving unification
problems. To fix it, add an extra parameter ``schema`` to ``StoreView``, and change
the type of ``SNil`` to be explicit that the ``empty`` is the function defined in
``DataStore``. Also add ``entry`` and ``store`` as explicit arguments to ``SAdd``:

.. code-block:: idris

    data StoreView : (schema : _) -> DataStore schema -> Type where
         SNil : StoreView schema DataStore.empty
         SAdd : (entry, store : _) -> (rec : StoreView schema store) ->
                StoreView schema (addToStore entry store)

Since ``size`` is as explicit argument in the ``DataStore`` record, it also needs
to be relevant in the type of ``storeViewHelp``:

.. code-block:: idris

    storeViewHelp : {size : _} ->
                    (items : Vect size (SchemaType schema)) ->
                    StoreView schema (MkData size items)

In ``TestStore.idr``:

+ In ``listItems``, ``empty`` needs to be ``DataStore.empty`` to be explicit that you
  mean the function
+ In ``filterKeys``, there is an error in the ``SNil`` case, which wasn't caught
  because of the type of ``SNil`` above. It should be:

.. code-block:: idris

      filterKeys test DataStore.empty | SNil = []

Chapter 11
----------

In ``Streams.idr`` add ``import Data.Stream`` for ``iterate``.

In ``Arith.idr`` and ``ArithTotal.idr``, the ``Divides`` view now has explicit
arguments for the dividend and remainder, so they need to be explicit in
``bound``:

.. code-block:: idris

    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy div rem prf) = rem + 1

In ``ArithCmd.idr``, update ``DivBy`` as above. Also add ``import Data.Strings`` for
``Strings.toLower``.

In ``ArithCmd.idr``, update ``DivBy`` and ``import Data.Strings`` as above. Also,
since export rules are per-namespace now, rather than per-file, you need to
export ``(>>=)`` from the namespaces ``CommandDo`` and ``ConsoleDo``.

In ``ArithCmdDo.idr``, since ``(>>=)`` is ``export``, ``Command`` and ``ConsoleIO``
also have to be ``export``.

In ``StreamFail.idr``, add a ``partial`` annotation to ``labelWith``.

Chapter 12
----------

For reasons described above: In ``ArithState.idr``, add ``import Data.Strings``.
Also the ``(>>=)`` operators need to be set as ``export`` since they are in their
own namespaces, and in ``getRandom``, ``DivBy`` needs to take additional
arguments ``div`` and ``rem``.

In ``ArithState.idr``, since ``(>>=)`` is ``export``, ``Command`` and ``ConsoleIO``
also have to be ``export``.

evalState from Control.Monad.State now takes the ``stateType`` argument first.

Chapter 13
----------

In ``StackIO.idr``:

+ ``tryAdd`` pattern matches on ``height``, so it needs to be written in its
  type:

.. code-block:: idris

    tryAdd : {height : _} -> StackIO height

+ ``height`` is also an implicit argument to ``stackCalc``, but is used by the
  definition, so add it to its type:

.. code-block:: idris

    stackCalc : {height : _} -> StackIO height

+ In ``StackDo`` namespace, export ``(>>=)``:

.. code-block:: idris

    namespace StackDo
      export
      (>>=) : StackCmd a height1 height2 ->
              (a -> Inf (StackIO height2)) -> StackIO height1
              (>>=) = Do

In ``Vending.idr``:

+ Add ``import Data.Strings`` and change ``cast`` to ``stringToNatOrZ`` in ``strToInput``
+ In ``MachineCmd`` type, add an implicit argument to ``(>>=)`` data constructor:

.. code-block:: idris

    (>>=) : {state2 : _} ->
            MachineCmd a state1 state2 ->
            (a -> MachineCmd b state2 state3) ->
            MachineCmd b state1 state3

+ In ``MachineIO`` type, add an implicit argument to ``Do`` data constructor:

.. code-block:: idris

    data MachineIO : VendState -> Type where
      Do : {state1 : _} ->
           MachineCmd a state1 state2 ->
           (a -> Inf (MachineIO state2)) -> MachineIO state1

+ ``runMachine`` pattern matches on ``inState``, so it needs to be written in its
  type:

.. code-block:: idris

    runMachine : {inState : _} -> MachineCmd ty inState outState -> IO ty

+ In ``MachineDo`` namespace, add an implicit argument to ``(>>=)`` and export it:

.. code-block:: idris

    namespace MachineDo
      export
      (>>=) : {state1 : _} ->
              MachineCmd a state1 state2 ->
              (a -> Inf (MachineIO state2)) -> MachineIO state1
      (>>=) = Do

+ ``vend`` and ``refill`` pattern match on ``pounds`` and ``chocs``, so they need to be written in
  their type:

.. code-block:: idris

    vend : {pounds : _} -> {chocs : _} -> MachineIO (pounds, chocs)
    refill: {pounds : _} -> {chocs : _} -> (num : Nat) -> MachineIO (pounds, chocs)

+ ``pounds`` and ``chocs`` are implicit arguments to ``machineLoop``, but are used by the
  definition, so add them to its type:

.. code-block:: idris

    machineLoop : {pounds : _} -> {chocs : _} -> MachineIO (pounds, chocs)

Chapter 14
----------

In ``ATM.idr``:

+ Add ``import Data.Strings`` and change ``cast`` to ``stringToNatOrZ`` in ``runATM``

In ``Hangman.idr``, add:

.. code-block:: idris

    import Data.Vect.Elem -- `Elem` now has its own submodule
    import Data.Strings -- for `toUpper`
    import Data.List -- for `nub`

+ In ``Loop`` namespace, export ``GameLoop`` type and its data constructors:

.. code-block:: idris

    namespace Loop
      public export
      data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
        (>>=) : GameCmd a state1 state2_fn ->
                ((res : a) -> Inf (GameLoop b (state2_fn res) state3_fn)) ->
                GameLoop b state1 state3_fn
        Exit : GameLoop () NotRunning (const NotRunning)

+ ``letters`` and ``guesses`` are used by ``gameLoop``, so they need to be written in its type:

.. code-block:: idris

    gameLoop : {letters : _} -> {guesses : _} ->
               GameLoop () (Running (S guesses) (S letters)) (const NotRunning)

+ In ``Game`` type, add an implicit argument ``letters`` to ``InProgress`` data constructor:

.. code-block:: idris

    data Game : GameState -> Type where
      GameStart : Game NotRunning
      GameWon : (word : String) -> Game NotRunning
      GameLost : (word : String) -> Game NotRunning
      InProgress : {letters : _} -> (word : String) -> (guesses : Nat) ->
                   (missing : Vect letters Char) -> Game (Running guesses letters)

+ ``removeElem`` pattern matches on ``n``, so it needs to be written in its type:

.. code-block:: idris

    removeElem : {n : _} ->
                 (value : a) -> (xs : Vect (S n) a) ->
                 {auto prf : Elem value xs} ->
                 Vect n a

Chapter 15
----------

.. todo::

   This chapter.
