module Idris.Doc.Keywords

import Decidable.Equality
import Parser.Lexer.Source
import Data.List.Quantifiers
import Data.String

import Idris.Doc.Annotations
import Idris.Pretty

import Libraries.Data.List.Quantifiers.Extra
import Libraries.Text.PrettyPrint.Prettyprinter


infix 10 ::=
data DocFor : String -> Type where
  (::=) : (0 str : String) -> (doc : Doc IdrisDocAnn) -> DocFor str

doc : DocFor _ -> Doc IdrisDocAnn
doc (_ ::= d) = d

fixity : Doc IdrisDocAnn
fixity = ""

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
    ```
    record Nat2 where
      constructor MkNat2
      fst : Nat
      snd : Nat
    ```
    """, "",
    """
    and we can then immediately use all of `fst`, `snd`, `{ fst := ?h1 }`,
    or `{snd $= ?h2 }` to respectively project values out of a record,
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
    ```
    data List a = Nil | (::) a (List a)
    ```
    """, "",
    """
    or a GADT-style definition for indexed types
    """, "",
    """
    ```
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
    Definitions can be individually declared `total`, `covering`, or partial`.
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
    header "if ... then ... else ..." :: ""
    :: map (indent 2) [
    """
    The `if ... then ... else ...` construct is dependently typed. This means
    that if you are branching over a variable, the branches will have refined
    types where that variable has been replaced by either `True` or `False`.
    For instance, in the following incomplete program
    """, "",
    """
    ```
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
    ```
    zeroIsNotOne : 0 === 1 -> Void
    zeroIsNotOne eq impossible
    ```
    """]

caseof : Doc IdrisDocAnn
caseof = "`case ... of ...` construct"

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
      ````
      f : (n : Nat) -> {auto _ : n === Z} -> Nat
      f n = n
      ````
      will only accept arguments that can be automatically proven to be equal
      to zero.
    """, "",
    """
    * `default` takes a value of the appropriate type and if no argument is
      explicitly passed at a call site, will use that default value.
      For instance, the following function
      ```
      f : {default 0 n : Nat} -> Nat
      f = n
      ```
      will return `0` if no argument is passed and its argument otherwise.
    """]

unused : Doc IdrisDocAnn
unused = "Currently unused keyword"

doblock : Doc IdrisDocAnn
doblock = vcat $
    header "Do block" :: ""
    :: map (indent 2) [
    #"""
    Do blocks are a popular way to structure (among other things) effectful code.
    They are desugared using `(>>=)` and `(>>)` respectively depending on whether
    the result of a subcomputation is bound. For instance the following block
    ```
      do x <- e1
         e2
         e3
    ```
    is equivalent to the expression `e1 >>= \ x => e2 >> e3`.
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
    ```
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

mutualblock : Doc IdrisDocAnn
mutualblock = vcat $
    header "Mutual block" :: ""
    :: map (indent 2) [
    """
    Mutual blocks allow users to have inter-dependent declarations. For instance
    we can define the `odd` and `even` checks in terms of each other like so:
    ```
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
    ```
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
    ```
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
    ```
    filter : (p : a -> Bool) -> List a -> List (x : a ** p x === True)
    filter p [] = []
    filter p (x :: xs) with (p x) proof eq
      _ | True = (x ** eq) :: filter p xs
      _ | False = filter p xs
    ```
    """]

keywordsDoc : All DocFor Source.keywords
keywordsDoc =
     "data" ::= datatypes
  :: "module" ::= "Keyword to start a module definition"
  :: "where" ::= whereblock
  :: "let" ::= "Keyword"
  :: "in" ::= "Used by `let` and `rewrite`. See either of them for more details."
  :: "do" ::= doblock
  :: "record" ::= recordtypes
  :: "auto" ::= implicitarg
  :: "default" ::= implicitarg
  :: "implicit" ::= unused
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
  :: "rewrite" ::= ""
  :: "using" ::= ""
  :: "interface" ::= ""
  :: "implementation" ::= ""
  :: "open" ::= unused
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
  = maybe (annotate (Syntax Keyword) $ pretty k) doc
  $ lookup k keywordsDoc
