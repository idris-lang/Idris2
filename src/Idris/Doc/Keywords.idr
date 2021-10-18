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

datatypes : Doc IdrisDocAnn
datatypes = vcat [ header "(Co)Data Types", "", indent 2
                """
                Keyword to introduce a (co)inductive type definition.
                You can either use a BNF-style definition for simple types
                ```
                data List a = Nil | (::) a (List a)
                ```
                or a GADT-style definition for indexed types
                ```
                data Vect : Nat -> Type -> Type where
                  Nil  : Vect 0 a
                  (::) : a -> Vect n a -> Vect (S n) a
                ```
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
visibility = ""

ifthenelse : Doc IdrisDocAnn
ifthenelse = ""

caseof : Doc IdrisDocAnn
caseof = ""

implicitarg : Doc IdrisDocAnn
implicitarg = ""

keywordsDoc : All DocFor Source.keywords
keywordsDoc =
     "data" ::= datatypes
  :: "module" ::= "Keyword"
  :: "where" ::= "Keyword"
  :: "let" ::= "Keyword"
  :: "in" ::= "Keyword"
  :: "do" ::= "Keyword"
  :: "record" ::= "Keyword"
  :: "auto" ::= implicitarg
  :: "default" ::= implicitarg
  :: "implicit" ::= ""
  :: "mutual" ::= ""
  :: "namespace" ::= ""
  :: "parameters" ::= ""
  :: "with" ::= ""
  :: "proof" ::= ""
  :: "impossible" ::= """
                      Keyword to dismiss a clause involving an argument with an
                      uninhabited type. For instance a proof that 0 is equal to 1:
                      ```
                      zeroIsNotOne : 0 === 1 -> Void
                      zeroIsNotOne eq impossible
                      ```
                      """
  :: "case" ::= caseof
  :: "of" ::= caseof
  :: "if" ::= ifthenelse
  :: "then" ::= ifthenelse
  :: "else" ::= ifthenelse
  :: "forall" ::= ""
  :: "rewrite" ::= ""
  :: "using" ::= ""
  :: "interface" ::= ""
  :: "implementation" ::= ""
  :: "open" ::= "Currently unused keyword"
  :: "import" ::= ""
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
