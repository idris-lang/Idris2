module Idris.Doc.Brackets

import Data.String
import Libraries.Data.String.Extra

import Idris.Doc.Annotations
import Idris.Syntax
import Idris.Pretty

export
getDocsForBracket : BracketType -> Doc IdrisDocAnn
getDocsForBracket IdiomBrackets = vcat $
    header "Idiom brackets" :: ""
    :: map (indent 2) [
    """
    Idiom brackets allow for easier application of `Applicative`s

    Adding two `Maybe Int`s can be written using `<*>` and `pure`

    ```idris
    addMaybe : Maybe Int -> Maybe Int -> Maybe Int
    addMaybe x y = pure (+) <*> x <*> y
    ```

    This can be expressed more concisely as:

    ```idris
    addMaybe : Maybe Int -> Maybe Int -> Maybe Int
    addMaybe x y= [| x + y |]
    ```
    """]
getDocsForBracket NameQuote = vcat $
    header "Name quotes" :: ""
    :: map (indent 2) [
    """
    Name quotes convert a raw name into a representation of a name.
    This allows elaborator scripts to refer to names the user provides.

    ```idris
    import Language.Reflection
    %language ElabReflection

    nameOfMaybe : Name
    nameOfMaybe = `{Maybe}
    ```

    Names can be qualified, however no disambiguation of names occurs when
    quoting them, so if you need a disambiguated name consider using
    `Language.Reflection.getType`.
    """]
getDocsForBracket TermQuote = vcat $
    header "Term quotes" :: ""
    :: map (indent 2) [
    """
    These allow an expression to be interpreted as a syntax tree rather than
    an actual expression, so it can be processed by an elaborator script
    for compile time codegen or meta-programming.

    ```idris
    import Language.Reflection
    %language ElabReflection

    helloWorld : TTImp
    helloWorld = `(putStrLn "hello world")
    ```
    """]
getDocsForBracket DeclQuote = vcat $
    header "Declaration quotes" :: ""
    :: map (indent 2) [
    """
    Declarations quotes allow multiple declaration
    (e.g. type declarations or function definitions) to be quoted

    These can then be passed to a elaborator script for compile time
    codegen or meta-programming.

    ```idris
    import Language.Reflection
    %language ElabReflection

    myProgram : List Decl
    myProgram = `[
        data Bool = False | True

        main : IO ()
        main = putStrLn "hello world"
    ]
    ```

    In this example, `main : IO ()` and
    `main = putStrLn "hello world"` are different `Decl`s
    """]
