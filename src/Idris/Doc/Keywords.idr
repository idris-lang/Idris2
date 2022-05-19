module Idris.Doc.Keywords

import Decidable.Equality
import Parser.Lexer.Source
import Data.List.Quantifiers
import Data.String

import Idris.Doc.Annotations
import Idris.Pretty

import Libraries.Data.List.Quantifiers.Extra
import Libraries.Data.String.Extra


infix 10 ::=
data DocFor : String -> Type where
  (::=) : (0 str : String) -> (doc : Doc IdrisDocAnn) -> DocFor str

doc : DocFor _ -> Doc IdrisDocAnn
doc (_ ::= d) = d

fixity : Doc IdrisDocAnn
fixity = vcat $
    header "Fixity declarations" :: ""
    :: map (indent 2) [
    """
    Operators can be assigned a priority level and associativity. During parsing
    operators with a higher priority will collect their arguments first and the
    declared associativity will inform how subterms are grouped.

    For instance the expression `a + b * c * d + e` is parsed as
    `(a + ((b * c) * d)) + e` because:
      `(+)` is at level 8 and associates to the left
      `(*)` is at level 9 and associates to the left
    """]

recordtypes : Doc IdrisDocAnn
recordtypes = vcat $
    header "Record types" :: ""
    :: map (indent 2) [
    """
    Records are data types with a single constructor. Each of the constructor's
    argument is given a name and the corresponding projections and record update
    functions are automatically generated.
    For instance, we can define a type of pairs of natural numbers
    """, "",
    """
    ```idris
    record Nat2 where
      constructor MkNat2
      fst : Nat
      snd : Nat
    ```
    """, "",
    """
    and we can then immediately use all of `fst`, `snd`, `{ fst := ?h1 }`,
    or `{ snd $= ?h2 }` to respectively project values out of a record,
    replace values, or update them.
    """
    ]

datatypes : Doc IdrisDocAnn
datatypes = vcat $
    header "(Co)Data types" :: ""
    :: map (indent 2) [
    """
    Keyword to introduce a (co)inductive type definition.
    You can either use a BNF-style definition for simple types
    """, "",
    """
    ```idris
    data List a = Nil | (::) a (List a)
    ```
    """, "",
    """
    or a GADT-style definition for indexed types
    """, "",
    """
    ```idris
    data Vect : Nat -> Type -> Type where
      Nil  : Vect 0 a
      (::) : a -> Vect n a -> Vect (S n) a
    ```
    """, "",
    """
    Coinductive data is introduced using the same syntax except
    that the type of potentially infinite subterms is wrapped in
    an `Inf` type constructor.
    """]

totality : Doc IdrisDocAnn
totality = vcat $
    header "Totality" :: ""
    :: map (indent 2) [
    """
    Definitions can be individually declared `total`, `covering`, or `partial`.
    It is also possible to set the default totality flag for definitions in a
    module by using the `%default` pragma.
    """, "",
    """
    * `total` offers the highest guarantees. Definitions using this flag are
      only accepted if:
        1. their patterns are covering all possible cases;
        2. they are either obviously terminating (for recursive functions)
           or productive (for corecursive functions);
        3. all the auxiliary functions used are total themselves.
    """, "",
    """
    * `covering` is the default level of guarantees. It only enforces that
      pattern matchings are exhaustive.
    """, "",
    """
    * `partial` is the absence of any totality requirement: as long as the
      definition typechecks, it is accepted. It is possible to call a partial
      function from a total one by using the `assert_total` escape hatch.
    """]

visibility : Doc IdrisDocAnn
visibility = vcat $
    header "Visibility" :: ""
    :: map (indent 2) [
    """
    Programmers can decide which parts of a module they expose to the outside
    world.
    """, "",
    """
    * `public export` ensures that both the declaration and the definition
       are accessible from the outside of the module. This means the function
       will be able to reduce in types.
    """, "",
    """
    * `export` means that only the declaration will be made available to the
      outside world. Users will be able to call the function but its internals
      will not be exposed because it will not reduce in types.
    """, "",
    """
    * `private` means that neither the declaration nor the definition will be
      exported. This is the default and is the ideal setting for auxiliary
      definitions.
    """]

ifthenelse : Doc IdrisDocAnn
ifthenelse = vcat $
    header "Boolean conditional" :: ""
    :: map (indent 2) [
    """
    The `if ... then ... else ...` construct is dependently typed. This means
    that if you are branching over a variable, the branches will have refined
    types where that variable has been replaced by either `True` or `False`.
    For instance, in the following incomplete program
    """, "",
    """
    ```idris
    notInvolutive : (b : Bool) -> not (not b) === b
    notInvolutive b = if b then ?holeTrue else ?holeFalse
    ```
    """, "",
    """
    the two holes have respective types `True === True` and `False === False`.
    """, "", "",
    """
    If you do not need the added power granted by dependently typed branches,
    consider using the simpler `ifThenElse` function defined in `Prelude`.
    """]

impossibility : Doc IdrisDocAnn
impossibility = vcat $
    header  "Impossible branches" :: ""
    :: map (indent 2) [
    """
    The `impossible` keyword can be used to dismiss a clause involving an
    argument with an uninhabited type. For instance an assumption stating
    that 0 is equal to 1:
    """, "",
    """
    ```idris
    zeroIsNotOne : 0 === 1 -> Void
    zeroIsNotOne eq impossible
    ```
    """]

caseof : Doc IdrisDocAnn
caseof = vcat $
    header "Case block" :: ""
    :: map (indent 2) [
    """
    The `case ... of ...` construct is dependently typed. This means that if you
    are branching over a variable, the branches will have refined types where
    that variable has been replaced by the appropriate pattern.
    For instance, in the following program
    """, "",
    """
    ```idris
    assoc : (ma, mb, mc : Maybe a) ->
            ((ma <|> mb) <|> mc) === (ma <|> (mb <|> mc))
    assoc ma mb mc = case ma of
      Nothing => Refl
      Just a  => Refl
    ```
    """, "",
    """
    the branches typecheck because in their respective types `ma` has been replaced
    either by `Nothing` or `Just a` and that was enough for them to compute to
    `(mb <|> mc) === (mb <|> mc)` and `Just a === Just a` respectively. Both of
    which can be discharged using `Refl`.
    """]

importing : Doc IdrisDocAnn
importing = vcat $
    header "Importing" :: ""
    :: map (indent 2) [
    """
    Importing a module brings the definition it exports into scope.
    Combined with `public` it also re-exports these definitions.
    """]

forallquantifier : Doc IdrisDocAnn
forallquantifier = vcat $
    header "Forall quantifier" :: ""
    :: map (indent 2) [
    """
    `forall` quantification is syntactic sugar for implicit runtime-irrelevant
    universal quantification. That is to say that `forall x, y, z. ...`
    desugars to `{0 x, y, z : _} -> ...`.
    """]

implicitarg : Doc IdrisDocAnn
implicitarg = vcat $
    header  "Implicit arguments" :: ""
    :: map (indent 2) [
    """
    Implicit arguments can be solved using various strategies. By default
    they will be filled in using unification but programmers can use various
    keywords to change that.
    """, "",
    """
    * `auto` will use the same mechanism as interface resolution to build the
      argument. Users can add new hints to the database by adding a `%hint`
      pragma to their declarations. By default all data constructors are hints.
      For instance, the following function
      ```idris
      f : (n : Nat) -> {auto _ : n === Z} -> Nat
      f n = n
      ```
      will only accept arguments that can be automatically proven to be equal
      to zero.
    """, "",
    """
    * `default` takes a value of the appropriate type and if no argument is
      explicitly passed at a call site, will use that default value.
      For instance, the following function
      ```idris
      f : {default 0 n : Nat} -> Nat
      f = n
      ```
      will return `0` if no argument is passed and its argument otherwise.
    """]

unusedKeyword : Doc IdrisDocAnn
unusedKeyword = "Currently unused keyword"

interfacemechanism : Doc IdrisDocAnn
interfacemechanism = vcat $
    header "Interfaces" :: ""
    :: map (indent 2) [
    """
    Interfaces offer ad-hoc polymorphism. Programmers can declare new
    interfaces offering a set of methods (some of which may have default
    implementations in terms of the interface's other methods) and write
    programs generic over all types implementing the interface.
    """, "",
    """
    In the following example we define a `Fail` interface that allows
    users to abort in case a computation is doomed to fail. We implement
    the `whenJust` construct using this interface and show a couple of
    implementations:
    """, "",
    """
    ```idris
    interface Fail (0 a : Type) where
      fail : a

    whenJust : Fail ret => Maybe a -> (a -> ret) -> ret
    whenJust (Just v) k = k v
    whenJust Nothing  _ = fail

    implementation Fail Bool where
      fail = False

    Fail (Maybe a) where
      fail = Nothing
    ```
    """, "",
    """
    As you can see the `implementation` keyword is optional. Note that the
    proof search machinery powering interface resolution works best if your
    implementations are for specific type constructors (here `Bool` and `Maybe`).
    """]

doblock : Doc IdrisDocAnn
doblock = vcat $
    header "Do block" :: ""
    :: map (indent 2) [
    #"""
    Do blocks are a popular way to structure (among other things) effectful code.
    They are desugared using `(>>=)` and `(>>)` respectively depending on whether
    the result of a subcomputation is bound. Let bindings and local definitions
    can be used (omitting `in` because the layout is already controlled by the
    `do`-based indentation) and desugared to the corresponding `let` constructs.

    For instance the following block
    ```idris
      do x <- e1
         e2
         let y = e3
         e4
    ```
    is equivalent to the expression `e1 >>= \ x => e2 >> let y = e3 in e4`.
    """#, "",
    """
    By default `(>>=)` and `(>>)` are then selected using the usual type
    directed disambiguation mechanisms. Users who want to bypass this implicit
    disambiguation step can use a qualified `do`: by writing `M.do` they ensure
    Idris will explicitly use `M.(>>=)` and `M.(>>)` during elaboration.
    """ ]

whereblock : Doc IdrisDocAnn
whereblock = vcat $
    header "Where block" :: ""
    :: map (indent 2) [
    header "NB:" <++> """
    `where` is used as a layout keyword in `data`, `record`, `interface`,
    and `implementation` blocks. This documentation snippet focuses instead
    on the `where` blocks introducing local definitions.
    """, "",
    """
    A `where` block allows the introduction of local auxiliary definitions
    that are parametrised over the variables bound on the left hand side of
    the parent clause (cf. the doc for `parameters`).
    """
    ]

parametersblock : Doc IdrisDocAnn
parametersblock = vcat $
    header "Parameters block" :: ""
    :: map (indent 2) [
    """
    Definitions that share a common parameter can be grouped in a parameters
    block to avoid having to explicitly pass it around. Outside of the block
    all the definitions will take additional arguments corresponding to the
    parameters. For instance the functions in the following block all use a
    default value `dflt`
    """, "",
    """
    ```idris
    parameters (dflt : a)

      head : List a -> a
      head (x :: xs) = x
      head _ = dflt

      last : List a -> a
      last [x] = x
      last (_ :: xs) = last xs
      last _ = dflt
    ```
    """, "",
    """
    and their respective types outside of the parameters block are
    `head : a -> List a -> a` and `last : a -> List a -> a`.
    """]

failblock : Doc IdrisDocAnn
failblock = vcat $
    header "Fail block" :: ""
    :: map (indent 2) [
    """
    Fail blocks let users check that some code parses but is rejected during elaboration.
    In the following example, we make sure that Idris rejects a proof that the character
    'a' is equal to 'b' by throwing an error when unifying them.
    """, "",
    """
    ```idris
    failing "When unifying"
      noteq : 'a' === 'b'
      noteq = Refl
    ```
    """, "",
    """
    If the (optional) string attached to a failing block does not appear in the error raised,
    or if no error is raised then the failing block is itself failing and thus leads to an error.
    This lets users document the kind of error the block is meant to document.
    """
    ]

mutualblock : Doc IdrisDocAnn
mutualblock = vcat $
    header "Mutual block" :: ""
    :: map (indent 2) [
    """
    Mutual blocks allow users to have inter-dependent declarations. For instance
    we can define the `odd` and `even` checks in terms of each other like so:
    ```idris
    mutual

      odd : Nat -> Bool
      odd Z = False
      odd (S n) = even n

      even : Nat -> Bool
      even Z = True
      even (S n) = odd n
    ```
    """, "",
    """
    Internally this is implemented in terms of the more fundamental
    forward-declaration feature: all the mutual declarations come first and then
    their definitions. In other words, the earlier example using a `mutual` block
    is equivalent to the following
    ```idris
    odd : Nat -> Bool
    even : Nat -> Bool

    odd Z = False
    odd (S n) = even n

    even Z = True
    even (S n) = odd n
    ```
    """]

namespaceblock : Doc IdrisDocAnn
namespaceblock = vcat $
    header "Namespace block" :: ""
    :: map (indent 2) [
    """
    Attempting to declare two functions with the same name in a given module
    will lead to a scope error. Putting each one in a different `namespace`
    block can help bypass this issue by ensuring that they are assigned distinct
    fully qualified names. For instance
    ```idris
    module M

    namespace Zero
      val : Nat
      val = 0

    namespace One
      val : Nat
      val = 1
    ```
    declares a module `M` containing two values `M.Zero.val` and `M.One.val`.
    You can use `export` or `public export` to control whether a function
    declared in a namespace is available outside of it.
    """]

rewriteeq : Doc IdrisDocAnn
rewriteeq = vcat $
    header "Rewrite" :: ""
    :: map (indent 2) [
    """
    Users can deploy an equality proof to adjust a type by replacing the value
    on the left hand side of the equality by that on the right hand side.
    For instance, if we know that the types `a` and `b` are propositionally
    equal, we can return a value of type `a` as if it had type `b`:
    ```idris
    transport : a === b -> a -> b
    transport eq x = rewrite sym eq in x
    ```
    """]

withabstraction : Doc IdrisDocAnn
withabstraction = vcat $
    header "With abstraction" :: ""
    :: map (indent 2) [
    """
    We often need to match on the result of an intermediate computation.
    When this intermediate computation additionally appears in the type of the
    function being defined, the `with` construct allows us to capture these
    occurences so that the observations made in the patterns will be reflected
    in the type.
    If we additionally need to remember that the link between the patterns and
    the intermediate computation we can use the `proof` keyword to retain an
    equality proof.
    """, "",
    """
    In the following example we want to implement a `filter` function that not
    only returns values that satisfy the input predicate but also proofs that
    they do. The `with (p x)` construct introduces a value of type `Bool`
    obtained by testing `x` with `p`. The additional `proof eq` part records in
    `eq` an equality proof stating that the `True`/`False` patterns in the further
    clauses are equal to the result of evaluating `p x`. This is the reason why
    we can successfully form `(x ** eq)` in the `True` branch.
    ```idris
    filter : (p : a -> Bool) -> List a -> List (x : a ** p x === True)
    filter p [] = []
    filter p (x :: xs) with (p x) proof eq
      _ | True = (x ** eq) :: filter p xs
      _ | False = filter p xs
    ```
    """]

letbinding : Doc IdrisDocAnn
letbinding = vcat $
    header "Let binding" :: ""
    :: map (indent 2) [
    """
    The `let` keyword is used for both local definitions and let bindings.
    Local definitions are just like top-level definitions except that they are
    defined in whatever extended context is available at the definition site.

    Let bindings can be used to bind the result of intermediate computations.
    They do not necessitate but can have a type annotation. They will not unfold
    in the type of subsequent terms so may not be appropriate in all cases.

    For instance, in the following definition the let-bound value `square`
    ensures that `n * n` is only computed once:
    ```idris
    power4 : Nat -> Nat
    power4 n = let square := n * n in square * square
    ```

    It is also possible to pattern-match on the result of the intermediate
    computation. The main pattern is written in place of the variable and
    an alternative list of clauses can be given using the `|` separator.
    For instance, we can shortcut the `square * square` computation in case
    the returned value is 0 like so:
    ```idris
    power4 : Nat -> Nat
    power4 n = let square@(S _) := n * n
                     | Z => Z
               in square * square
    ```
    """]

keywordsDoc : All DocFor Source.keywords
keywordsDoc =
     "data" ::= datatypes
  :: "module" ::= "Keyword to start a module definition"
  :: "where" ::= whereblock
  :: "let" ::= letbinding
  :: "in" ::= "Used by `let` and `rewrite`. See either of them for more details."
  :: "do" ::= doblock
  :: "record" ::= recordtypes
  :: "auto" ::= implicitarg
  :: "default" ::= implicitarg
  :: "implicit" ::= unusedKeyword
  :: "failing" ::= failblock
  :: "mutual" ::= mutualblock
  :: "namespace" ::= namespaceblock
  :: "parameters" ::= parametersblock
  :: "with" ::= withabstraction
  :: "proof" ::= withabstraction
  :: "impossible" ::= impossibility
  :: "case" ::= caseof
  :: "of" ::= caseof
  :: "if" ::= ifthenelse
  :: "then" ::= ifthenelse
  :: "else" ::= ifthenelse
  :: "forall" ::= forallquantifier
  :: "rewrite" ::= rewriteeq
  :: "using" ::= ""
  :: "interface" ::= interfacemechanism
  :: "implementation" ::= interfacemechanism
  :: "open" ::= unusedKeyword
  :: "import" ::= importing
  :: "public" ::= visibility
  :: "export" ::= visibility
  :: "private" ::= visibility
  :: "infixl" ::= fixity
  :: "infixr" ::= fixity
  :: "infix" ::= fixity
  :: "prefix" ::= fixity
  :: "total" ::= totality
  :: "partial" ::= totality
  :: "covering" ::= totality
  :: []

export
getDocsForKeyword : String -> Doc IdrisDocAnn
getDocsForKeyword k
  = maybe (annotate (Syntax Keyword) $ pretty0 k) doc
  $ lookup k keywordsDoc


unusedSymbol : Doc IdrisDocAnn
unusedSymbol = "Currently unused symbol"

lambdaAbstraction : Doc IdrisDocAnn
lambdaAbstraction = """
  An anonymous function is introduced using a lambda `\\` and binds a
  comma-separated list of either variable names or irrefutable patterns
  before returning a right hand side using `=>`.

  For instance we can implement `transport` like so:
  ```
  transport : a === b -> a -> b
  transport = \\ Refl, v => v
  ```
  """

fatArrow : Doc IdrisDocAnn
fatArrow = vcat
  [ """
    Used for an interface constraint in a type signature or as part of a
    lambda abstraction or case block.

    1. Interface constraint
    """
  , indent 2 """
    `a => b` corresponds to `{auto _ : a} -> b`
    """, ""
  , """
    2. Lambda abstraction
    """
  , indent 2 lambdaAbstraction
  , "", """
    3. Case block
    """
  ]

bang : Doc IdrisDocAnn
bang = """
  Directive to lift the following effectful expression to the nearest enclosing
  (potentially implicit) `do` block. In the following definition for instance

  ```
  anyM : Monad m => (a -> m Bool) -> List a -> m (Maybe a)
  anyM p [] = pure Nothing
  anyM p (x :: xs) = if !(p x) then pure (Just x) else anyM p xs
  ```

  the expression `if !(p x) then pure (Just x) else anyM p xs` is equivalent to
  the following `do` block:

  ```
  do b <- p x
     if b then pure (Just x) else anyM p xs
  ```
  """

asPattern : Doc IdrisDocAnn
asPattern = """
  An as pattern `@` can be used to both pattern match on a variable
  and retain a name for the compound expression. E.g. instead of writing
  ```
  last : List a -> Maybe a
  last [] = Nothing
  last [x] = Just x
  last (x :: y :: ys) = last (y :: ys)
  ```

  where, in the last clasue, we take `y :: ys` apart on the left hand side
  before reconstructing it on the right hand side, we can write:

  ```
  last (x :: xs@(_ :: _)) = last xs
  ```
  """

tupleSyntax : Doc IdrisDocAnn
tupleSyntax = "Used to build dependent pairs together with parentheses"

rangeSyntax : Doc IdrisDocAnn
rangeSyntax = """
  The ellipsis `..` can be used to generate lists or streams of values for
  types that implement the `Range` interface.

  Lists can be generated using an initial value, an (optional) second value
  and a final one. For instance, we can generate lists of integers like so:
    1. `[1..5]`   evaluates to `[1,2,3,4,5]`
    2. `[1,3..5]` evaluates to `[1, 3, 5]`

  Streams can be generated using an initial value and an optional second value.
  For instance the following streams of integers:
    1. `[1..]`   for all positive integers
    2. `[1,3..]` for all positive odds
  """

recordUpdate : Doc IdrisDocAnn
recordUpdate = vcat $ header "Record updates" :: ""
  :: map (indent 2) [
  """
  If a record `r` has a field `n` of type `Nat`, it is possible to either

  1. overwrite the current value with `0` by using the assignment symbol `:=`
     like so: `{ n := 0 } r`

  2. modify the current value by adding `2` by using the modification symbol `$=`
     like so: `{ n $= (2 +) } r`.

  Multiple updates can be combined in a single update by grouping a comma-separated
  list of assignments and/or modifications like so: `{ a := Z, b $= S } r`.
  """
  ]

symbolsDoc : All DocFor (Source.symbols ++ Source.reservedInfixSymbols)
symbolsDoc
  = "," ::= ""
  :: ";" ::= ""
  :: "_" ::= """
             An implicit value either solved by unification or bound
             as a pattern or type variable.
             """
  :: "`" ::= ""
  :: "%" ::= "Start of a pragma"
  :: "\\" ::= lambdaAbstraction
  :: ":" ::= """
             Type declaration, for instance `id : a -> a`
             declares a new toplevel definition `id` of type `a -> a`.
             """
  :: "=" ::= "Definition or equality type"
  :: ":=" ::= "Let binding or record assignment"
  :: "$=" ::= recordUpdate
  :: "|" ::= "Additional patterns showing up in a `with` clause"
  :: "|||" ::= "Document string attached to the following definition"
  :: "<-" ::= "Bind in a do block"
  :: "->" ::= "Function type"
  :: "=>" ::= fatArrow
  :: "?" ::= "An implicit value solved by unification."
  :: "!" ::= bang
  :: "&" ::= unusedSymbol
  :: "**" ::= tupleSyntax
  :: ".." ::= rangeSyntax
  :: "~" ::= ""
  :: "@" ::= asPattern
  :: []

export
getDocsForSymbol : String -> Doc IdrisDocAnn
getDocsForSymbol k
  = maybe (annotate (Syntax Keyword) $ pretty0 k) doc
  $ lookup k symbolsDoc
