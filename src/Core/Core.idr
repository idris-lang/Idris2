module Core.Core

import Core.Env
import Core.TT

import Data.List
import Data.List1
import Data.Vect

import Libraries.Data.IMaybe
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util

import public Data.IORef
import System
import System.File

%default covering

public export
data TTCErrorMsg
    = Format String Int Int
    | EndOfBuffer String
    | Corrupt String

public export
data CaseError = DifferingArgNumbers
               | DifferingTypes
               | MatchErased (vars ** (Env Term vars, Term vars))
               | NotFullyApplied Name
               | UnknownType

public export
data DotReason = NonLinearVar
               | VarApplied
               | NotConstructor
               | ErasedArg
               | UserDotted
               | UnknownDot
               | UnderAppliedCon

export
Show DotReason where
  show NonLinearVar = "Non linear pattern variable"
  show VarApplied = "Variable applied to arguments"
  show NotConstructor = "Not a constructor application or primitive"
  show ErasedArg = "Erased argument"
  show UserDotted = "User dotted"
  show UnknownDot = "Unknown reason"
  show UnderAppliedCon = "Under-applied constructor"

export
Pretty DotReason where
  pretty NonLinearVar = reflow "Non linear pattern variable"
  pretty VarApplied = reflow "Variable applied to arguments"
  pretty NotConstructor = reflow "Not a constructor application or primitive"
  pretty ErasedArg = reflow "Erased argument"
  pretty UserDotted = reflow "User dotted"
  pretty UnknownDot = reflow "Unknown reason"
  pretty UnderAppliedCon = reflow "Under-applied constructor"

-- All possible errors, carrying a location
public export
data Error : Type where
     Fatal : Error -> Error -- flag as unrecoverable (so don't postpone awaiting further info)
     CantConvert : {vars : _} ->
                   FC -> Env Term vars -> Term vars -> Term vars -> Error
     CantSolveEq : {vars : _} ->
                   FC -> Env Term vars -> Term vars -> Term vars -> Error
     PatternVariableUnifies : {vars : _} ->
                              FC -> Env Term vars -> Name -> Term vars -> Error
     CyclicMeta : {vars : _} ->
                  FC -> Env Term vars -> Name -> Term vars -> Error
     WhenUnifying : {vars : _} ->
                    FC -> Env Term vars -> Term vars -> Term vars -> Error -> Error
     ValidCase : {vars : _} ->
                 FC -> Env Term vars -> Either (Term vars) Error -> Error
     UndefinedName : FC -> Name -> Error
     InvisibleName : FC -> Name -> Maybe Namespace -> Error
     BadTypeConType : FC -> Name -> Error
     BadDataConType : FC -> Name -> Name -> Error
     NotCovering : FC -> Name -> Covering -> Error
     NotTotal : FC -> Name -> PartialReason -> Error
     LinearUsed : FC -> Nat -> Name -> Error
     LinearMisuse : FC -> Name -> RigCount -> RigCount -> Error
     BorrowPartial : {vars : _} ->
                     FC -> Env Term vars -> Term vars -> Term vars -> Error
     BorrowPartialType : {vars : _} ->
                         FC -> Env Term vars -> Term vars -> Error
     AmbiguousName : FC -> List Name -> Error
     AmbiguousElab : {vars : _} ->
                     FC -> Env Term vars -> List (Term vars) -> Error
     AmbiguousSearch : {vars : _} ->
                       FC -> Env Term vars -> Term vars -> List (Term vars) -> Error
     AmbiguityTooDeep : FC -> Name -> List Name -> Error
     AllFailed : List (Maybe Name, Error) -> Error
     RecordTypeNeeded : {vars : _} ->
                        FC -> Env Term vars -> Error
     NotRecordField : FC -> String -> Maybe Name -> Error
     NotRecordType : FC -> Name -> Error
     IncompatibleFieldUpdate : FC -> List String -> Error
     InvalidArgs : {vars : _} ->
                        FC -> Env Term vars -> List Name -> Term vars -> Error
     TryWithImplicits : {vars : _} ->
                        FC -> Env Term vars -> List (Name, Term vars) -> Error
     BadUnboundImplicit : {vars : _} ->
                          FC -> Env Term vars -> Name -> Term vars -> Error
     CantSolveGoal : {vars : _} ->
                     FC -> Env Term vars -> Term vars -> Error
     DeterminingArg : {vars : _} ->
                      FC -> Name -> Int -> Env Term vars -> Term vars -> Error
     UnsolvedHoles : List (FC, Name) -> Error
     CantInferArgType : {vars : _} ->
                        FC -> Env Term vars -> Name -> Name -> Term vars -> Error
     SolvedNamedHole : {vars : _} ->
                       FC -> Env Term vars -> Name -> Term vars -> Error
     VisibilityError : FC -> Visibility -> Name -> Visibility -> Name -> Error
     NonLinearPattern : FC -> Name -> Error
     BadPattern : FC -> Name -> Error
     NoDeclaration : FC -> Name -> Error
     AlreadyDefined : FC -> Name -> Error
     NotFunctionType : {vars : _} ->
                       FC -> Env Term vars -> Term vars -> Error
     RewriteNoChange : {vars : _} ->
                       FC -> Env Term vars -> Term vars -> Term vars -> Error
     NotRewriteRule : {vars : _} ->
                      FC -> Env Term vars -> Term vars -> Error
     CaseCompile : FC -> Name -> CaseError -> Error

     MatchTooSpecific : {vars : _} ->
                        FC -> Env Term vars -> Term vars -> Error
     BadDotPattern : {vars : _} ->
                     FC -> Env Term vars -> DotReason -> Term vars -> Term vars -> Error
     BadImplicit : FC -> String -> Error
     BadRunElab : {vars : _} ->
                  FC -> Env Term vars -> Term vars -> Error
     GenericMsg : FC -> String -> Error
     TTCError : TTCErrorMsg -> Error
     FileErr : String -> FileError -> Error
     CantFindPackage : String -> Error
     LitFail : FC -> Error
     LexFail : FC -> String -> Error
     ParseFail : FC -> String -> Error
     ModuleNotFound : FC -> ModuleIdent -> Error
     CyclicImports : List ModuleIdent -> Error
     ForceNeeded : Error
     InternalError : String -> Error
     UserError : String -> Error
     NoForeignCC : FC -> Error
     BadMultiline : FC -> String -> Error

     InType : FC -> Name -> Error -> Error
     InCon : FC -> Name -> Error -> Error
     InLHS : FC -> Name -> Error -> Error
     InRHS : FC -> Name -> Error -> Error

     MaybeMisspelling : Error -> List1 String -> Error

public export
data Warning : Type where
     UnreachableClause : {vars : _} ->
                         FC -> Env Term vars -> Term vars -> Warning
     Deprecated : String -> Warning

export
Show TTCErrorMsg where
  show (Format file ver exp) =
    let age = if ver < exp then "older" else "newer" in
        "TTC data is in an " ++ age ++ " format, file: " ++ file ++ ", expected version: " ++ show exp ++ ", actual version: " ++ show ver
  show (EndOfBuffer when) = "End of buffer when reading " ++ when
  show (Corrupt ty) = "Corrupt TTC data for " ++ ty

-- Simplest possible display - higher level languages should unelaborate names
-- and display annotations appropriately
export
Show Error where
  show (Fatal err) = show err
  show (CantConvert fc env x y)
      = show fc ++ ":Type mismatch: " ++ show x ++ " and " ++ show y
  show (CantSolveEq fc env x y)
      = show fc ++ ":" ++ show x ++ " and " ++ show y ++ " are not equal"
  show (PatternVariableUnifies fc env n x)
      = show fc ++ ":Pattern variable " ++ show n ++ " unifies with " ++ show x
  show (CyclicMeta fc env n tm)
      = show fc ++ ":Cycle detected in metavariable solution " ++ show n
             ++ " = " ++ show tm
  show (WhenUnifying fc _ x y err)
      = show fc ++ ":When unifying: " ++ show x ++ " and " ++ show y ++ "\n\t" ++ show err
  show (ValidCase fc _ prob)
      = show fc ++ ":" ++
           case prob of
             Left tm => assert_total (show tm) ++ " is not a valid impossible pattern because it typechecks"
             Right err => "Not a valid impossible pattern:\n\t" ++ assert_total (show err)
  show (UndefinedName fc x)
    = show fc ++ ":Undefined name " ++ show x
  show (InvisibleName fc x (Just ns))
       = show fc ++ ":Name " ++ show x ++ " is inaccessible since " ++
         show ns ++ " is not explicitly imported"
  show (InvisibleName fc x _) = show fc ++ ":Name " ++ show x ++ " is private"
  show (BadTypeConType fc n)
       = show fc ++ ":Return type of " ++ show n ++ " must be Type"
  show (BadDataConType fc n fam)
       = show fc ++ ":Return type of " ++ show n ++ " must be in " ++ show fam
  show (NotCovering fc n cov)
       = show fc ++ ":" ++ show n ++ " is not covering:\n\t" ++
            case cov of
                 IsCovering => "Oh yes it is (Internal error!)"
                 MissingCases cs => "Missing cases:\n\t" ++
                                           showSep "\n\t" (map show cs)
                 NonCoveringCall ns => "Calls non covering function"
                                           ++ (case ns of
                                                   [fn] => " " ++ show fn
                                                   _ => "s: " ++ showSep ", " (map show ns))

  show (NotTotal fc n r)
       = show fc ++ ":" ++ show n ++ " is not total"
  show (LinearUsed fc count n)
      = show fc ++ ":There are " ++ show count ++ " uses of linear name " ++ show n
  show (LinearMisuse fc n exp ctx)
      = show fc ++ ":Trying to use " ++ showRig exp ++ " name " ++ show n ++
                   " in " ++ showRel ctx ++ " context"
     where
       showRig : RigCount -> String
       showRig = elimSemi
         "linear"
         "irrelevant"
         (const "unrestricted")

       showRel : RigCount -> String
       showRel = elimSemi
         "relevant"
         "irrelevant"
         (const "non-linear")
  show (BorrowPartial fc env t arg)
      = show fc ++ ":" ++ show t ++ " borrows argument " ++ show arg ++
                   " so must be fully applied"
  show (BorrowPartialType fc env t)
      = show fc ++ ":" ++ show t ++ " borrows, so must return a concrete type"

  show (AmbiguousName fc ns) = show fc ++ ":Ambiguous name " ++ show ns
  show (AmbiguousElab fc env ts) = show fc ++ ":Ambiguous elaboration " ++ show ts
  show (AmbiguousSearch fc env tgt ts) = show fc ++ ":Ambiguous search " ++ show ts
  show (AmbiguityTooDeep fc n ns)
      = show fc ++ ":Ambiguity too deep in " ++ show n ++ " " ++ show ns
  show (AllFailed ts) = "No successful elaboration: " ++ assert_total (show ts)
  show (RecordTypeNeeded fc env)
      = show fc ++ ":Can't infer type of record to update"
  show (NotRecordField fc fld Nothing)
      = show fc ++ ":" ++ fld ++ " is not part of a record type"
  show (NotRecordField fc fld (Just ty))
      = show fc ++ ":Record type " ++ show ty ++ " has no field " ++ fld
  show (NotRecordType fc ty)
      = show fc ++ ":" ++ show ty ++ " is not a record type"
  show (IncompatibleFieldUpdate fc flds)
      = show fc ++ ":Field update " ++ showSep "->" flds ++ " not compatible with other updates"
  show (InvalidArgs fc env ns tm)
     = show fc ++ ":" ++ show ns ++ " are not valid arguments in " ++ show tm
  show (TryWithImplicits fc env imps)
     = show fc ++ ":Need to bind implicits "
          ++ showSep "," (map (\x => show (fst x) ++ " : " ++ show (snd x)) imps)
          ++ "\n(The front end should probably have done this for you. Please report!)"
  show (BadUnboundImplicit fc env n ty)
      = show fc ++ ":Can't bind name " ++ nameRoot n ++
                   " with type " ++ show ty
  show (CantSolveGoal fc env g)
      = show fc ++ ":Can't solve goal " ++ assert_total (show g)
  show (DeterminingArg fc n i env g)
      = show fc ++ ":Can't solve goal " ++ assert_total (show g) ++
                " since argument " ++ show n ++ " can't be inferred"
  show (UnsolvedHoles hs) = "Unsolved holes " ++ show hs
  show (CantInferArgType fc env n h ty)
      = show fc ++ ":Can't infer type for " ++ show n ++
                   " (got " ++ show ty ++ " with hole " ++ show h ++ ")"
  show (SolvedNamedHole fc _ h _) = show fc ++ ":Named hole " ++ show h ++ " is solved by unification"
  show (VisibilityError fc vx x vy y)
      = show fc ++ ":" ++ show vx ++ " " ++ show x ++ " cannot refer to "
                       ++ show vy ++ " " ++ show y
  show (NonLinearPattern fc n) = show fc ++ ":Non linear pattern variable " ++ show n
  show (BadPattern fc n) = show fc ++ ":Pattern not allowed here: " ++ show n
  show (NoDeclaration fc x) = show fc ++ ":No type declaration for " ++ show x
  show (AlreadyDefined fc x) = show fc ++ ":" ++ show x ++ " is already defined"
  show (NotFunctionType fc env tm) = show fc ++ ":Not a function type: " ++ show tm
  show (RewriteNoChange fc env rule ty)
      = show fc ++ ":Rewriting by " ++ show rule ++ " did not change type " ++ show ty
  show (NotRewriteRule fc env rule)
      = show fc ++ ":" ++ show rule ++ " is not a rewrite rule type"
  show (CaseCompile fc n DifferingArgNumbers)
      = show fc ++ ":Patterns for " ++ show n ++ " have different numbers of arguments"
  show (CaseCompile fc n DifferingTypes)
      = show fc ++ ":Patterns for " ++ show n ++ " require matching on different types"
  show (CaseCompile fc n UnknownType)
      = show fc ++ ":Can't infer type to match in " ++ show n
  show (CaseCompile fc n (MatchErased (_ ** (env, tm))))
      = show fc ++ ":Attempt to match on erased argument " ++ show tm ++
                   " in " ++ show n
  show (CaseCompile fc n (NotFullyApplied c))
      = show fc ++ ":Constructor " ++ show c ++ " is not fully applied"
  show (MatchTooSpecific fc env tm)
      = show fc ++ ":Can't match on " ++ show tm ++ " as it is has a polymorphic type"
  show (BadDotPattern fc env reason x y)
      = show fc ++ ":Can't match on " ++ show x ++
           " (" ++ show reason ++ ")" ++
           " - it elaborates to " ++ show y
  show (BadImplicit fc str) = show fc ++ ":" ++ str ++ " can't be bound here"
  show (BadRunElab fc env script) = show fc ++ ":Bad elaborator script " ++ show script
  show (GenericMsg fc str) = show fc ++ ":" ++ str
  show (TTCError msg) = "Error in TTC file: " ++ show msg
  show (FileErr fname err) = "File error (" ++ fname ++ "): " ++ show err
  show (CantFindPackage fname) = "Can't find package " ++ fname
  show (LitFail fc) = show fc ++ ":Can't parse literate"
  show (LexFail fc err) = show fc ++ ":Lexer error (" ++ show err ++ ")"
  show (ParseFail fc err) = "Parse error (" ++ show err ++ ")"
  show (ModuleNotFound fc ns)
      = show fc ++ ":" ++ show ns ++ " not found"
  show (CyclicImports ns)
      = "Module imports form a cycle: " ++ showSep " -> " (map show ns)
  show ForceNeeded = "Internal error when resolving implicit laziness"
  show (InternalError str) = "INTERNAL ERROR: " ++ str
  show (UserError str) = "Error: " ++ str
  show (NoForeignCC fc) = show fc ++
       ":The given specifier was not accepted by any available backend."
  show (BadMultiline fc str) = "Invalid multiline string: " ++ str

  show (InType fc n err)
       = show fc ++ ":When elaborating type of " ++ show n ++ ":\n" ++
         show err
  show (InCon fc n err)
       = show fc ++ ":When elaborating type of constructor " ++ show n ++ ":\n" ++
         show err
  show (InLHS fc n err)
       = show fc ++ ":When elaborating left hand side of " ++ show n ++ ":\n" ++
         show err
  show (InRHS fc n err)
       = show fc ++ ":When elaborating right hand side of " ++ show n ++ ":\n" ++
         show err

  show (MaybeMisspelling err ns)
     = show err ++ "\nDid you mean" ++ case ns of
         (n ::: []) => ": " ++ n ++ "?"
         _ => " any of: " ++ showSep ", " (map show (forget ns)) ++ "?"
export
getErrorLoc : Error -> Maybe FC
getErrorLoc (Fatal err) = getErrorLoc err
getErrorLoc (CantConvert loc _ _ _) = Just loc
getErrorLoc (CantSolveEq loc _ _ _) = Just loc
getErrorLoc (PatternVariableUnifies loc _ _ _) = Just loc
getErrorLoc (CyclicMeta loc _ _ _) = Just loc
getErrorLoc (WhenUnifying loc _ _ _ _) = Just loc
getErrorLoc (ValidCase loc _ _) = Just loc
getErrorLoc (UndefinedName loc _) = Just loc
getErrorLoc (InvisibleName loc _ _) = Just loc
getErrorLoc (BadTypeConType loc _) = Just loc
getErrorLoc (BadDataConType loc _ _) = Just loc
getErrorLoc (NotCovering loc _ _) = Just loc
getErrorLoc (NotTotal loc _ _) = Just loc
getErrorLoc (LinearUsed loc _ _) = Just loc
getErrorLoc (LinearMisuse loc _ _ _) = Just loc
getErrorLoc (BorrowPartial loc _ _ _) = Just loc
getErrorLoc (BorrowPartialType loc _ _) = Just loc
getErrorLoc (AmbiguousName loc _) = Just loc
getErrorLoc (AmbiguousElab loc _ _) = Just loc
getErrorLoc (AmbiguousSearch loc _ _ _) = Just loc
getErrorLoc (AmbiguityTooDeep loc _ _) = Just loc
getErrorLoc (AllFailed ((_, x) :: _)) = getErrorLoc x
getErrorLoc (AllFailed []) = Nothing
getErrorLoc (RecordTypeNeeded loc _) = Just loc
getErrorLoc (NotRecordField loc _ _) = Just loc
getErrorLoc (NotRecordType loc _) = Just loc
getErrorLoc (IncompatibleFieldUpdate loc _) = Just loc
getErrorLoc (InvalidArgs loc _ _ _) = Just loc
getErrorLoc (TryWithImplicits loc _ _) = Just loc
getErrorLoc (BadUnboundImplicit loc _ _ _) = Just loc
getErrorLoc (CantSolveGoal loc _ _) = Just loc
getErrorLoc (DeterminingArg loc _ _ _ _) = Just loc
getErrorLoc (UnsolvedHoles ((loc, _) :: _)) = Just loc
getErrorLoc (UnsolvedHoles []) = Nothing
getErrorLoc (CantInferArgType loc _ _ _ _) = Just loc
getErrorLoc (SolvedNamedHole loc _ _ _) = Just loc
getErrorLoc (VisibilityError loc _ _ _ _) = Just loc
getErrorLoc (NonLinearPattern loc _) = Just loc
getErrorLoc (BadPattern loc _) = Just loc
getErrorLoc (NoDeclaration loc _) = Just loc
getErrorLoc (AlreadyDefined loc _) = Just loc
getErrorLoc (NotFunctionType loc _ _) = Just loc
getErrorLoc (RewriteNoChange loc _ _ _) = Just loc
getErrorLoc (NotRewriteRule loc _ _) = Just loc
getErrorLoc (CaseCompile loc _ _) = Just loc
getErrorLoc (MatchTooSpecific loc _ _) = Just loc
getErrorLoc (BadDotPattern loc _ _ _ _) = Just loc
getErrorLoc (BadImplicit loc _) = Just loc
getErrorLoc (BadRunElab loc _ _) = Just loc
getErrorLoc (GenericMsg loc _) = Just loc
getErrorLoc (TTCError _) = Nothing
getErrorLoc (FileErr _ _) = Nothing
getErrorLoc (CantFindPackage _) = Nothing
getErrorLoc (LitFail loc) = Just loc
getErrorLoc (LexFail loc _) = Just loc
getErrorLoc (ParseFail loc _) = Just loc
getErrorLoc (ModuleNotFound loc _) = Just loc
getErrorLoc (CyclicImports _) = Nothing
getErrorLoc ForceNeeded = Nothing
getErrorLoc (InternalError _) = Nothing
getErrorLoc (UserError _) = Nothing
getErrorLoc (NoForeignCC loc) = Just loc
getErrorLoc (BadMultiline loc _) = Just loc
getErrorLoc (InType _ _ err) = getErrorLoc err
getErrorLoc (InCon _ _ err) = getErrorLoc err
getErrorLoc (InLHS _ _ err) = getErrorLoc err
getErrorLoc (InRHS _ _ err) = getErrorLoc err
getErrorLoc (MaybeMisspelling err _) = getErrorLoc err

export
getWarningLoc : Warning -> Maybe FC
getWarningLoc (UnreachableClause fc _ _) = Just fc
getWarningLoc (Deprecated _) = Nothing

-- Core is a wrapper around IO that is specialised for efficiency.
export
record Core t where
  constructor MkCore
  runCore : IO (Either Error t)

export
coreRun : Core a ->
          (Error -> IO b) -> (a -> IO b) -> IO b
coreRun (MkCore act) err ok
    = either err ok !act

export
coreFail : Error -> Core a
coreFail e = MkCore (pure (Left e))

export
wrapError : (Error -> Error) -> Core a -> Core a
wrapError fe (MkCore prog)
    = MkCore (prog >>=
                 (\x => case x of
                             Left err => pure (Left (fe err))
                             Right val => pure (Right val)))

-- This would be better if we restrict it to a limited set of IO operations
export
%inline
coreLift : IO a -> Core a
coreLift op = MkCore (do op' <- op
                         pure (Right op'))

{- Monad, Applicative, Traversable are specialised by hand for Core.
In theory, this shouldn't be necessary, but it turns out that Idris 1 doesn't
specialise interfaces under 'case' expressions, and this has a significant
impact on both compile time and run time.

Of course it would be a good idea to fix this in Idris, but it's not an urgent
thing on the road to self hosting, and we can make sure this isn't a problem
in the next version (i.e., in this project...)! -}

-- Functor (specialised)
export %inline
map : (a -> b) -> Core a -> Core b
map f (MkCore a) = MkCore (map (map f) a)

export %inline
(<$>) : (a -> b) -> Core a -> Core b
(<$>) f (MkCore a) = MkCore (map (map f) a)

export %inline
ignore : Core a -> Core ()
ignore = map (\ _ => ())

-- This would be better if we restrict it to a limited set of IO operations
export
%inline
coreLift_ : IO a -> Core ()
coreLift_ op = ignore (coreLift op)

-- Monad (specialised)
export %inline
(>>=) : Core a -> (a -> Core b) -> Core b
(>>=) (MkCore act) f
    = MkCore (act >>=
                   (\x => case x of
                               Left err => pure (Left err)
                               Right val => runCore (f val)))

export %inline
(>>) : Core () -> Core a -> Core a
ma >> mb = ma >>= const mb

-- Flipped bind
infixr 1 =<<
export %inline
(=<<) : (a -> Core b) -> Core a -> Core b
(=<<) = flip (>>=)

-- Kleisli compose
infixr 1 >=>
export %inline
(>=>) : (a -> Core b) -> (b -> Core c) -> (a -> Core c)
f >=> g = (g =<<) . f

-- Flipped kleisli compose
infixr 1 <=<
export %inline
(<=<) : (b -> Core c) -> (a -> Core b) -> (a -> Core c)
(<=<) = flip (>=>)

-- Applicative (specialised)
export %inline
pure : a -> Core a
pure x = MkCore (pure (pure x))

export
(<*>) : Core (a -> b) -> Core a -> Core b
(<*>) (MkCore f) (MkCore a) = MkCore [| f <*> a |]

export
(*>) : Core a -> Core b -> Core b
(*>) (MkCore a) (MkCore b) = MkCore [| a *> b |]

export
(<*) : Core a -> Core b -> Core a
(<*) (MkCore a) (MkCore b) = MkCore [| a <* b |]

export %inline
when : Bool -> Lazy (Core ()) -> Core ()
when True f = f
when False f = pure ()


export %inline
unless : Bool -> Lazy (Core ()) -> Core ()
unless = when . not

export
iwhen : (b : Bool) -> Lazy (Core a) -> Core (IMaybe b a)
iwhen True f = Just <$> f
iwhen False _ = pure Nothing

export
iunless : (b : Bool) -> Lazy (Core a) -> Core (IMaybe (not b) a)
iunless b f = iwhen (not b) f

export %inline
whenJust : Maybe a -> (a -> Core ()) -> Core ()
whenJust (Just a) k = k a
whenJust Nothing k = pure ()

export
iwhenJust : IMaybe b a -> (a -> Core ()) -> Core ()
iwhenJust (Just a) k = k a
iwhenJust Nothing k = pure ()

-- Control.Catchable in Idris 1, just copied here (but maybe no need for
-- it since we'll only have the one instance for Core Error...)
public export
interface Catchable m t | m where
    throw : {0 a : Type} -> t -> m a
    catch : m a -> (t -> m a) -> m a

export
Catchable Core Error where
  catch (MkCore prog) h
      = MkCore ( do p' <- prog
                    case p' of
                         Left e => let MkCore he = h e in he
                         Right val => pure (Right val))
  throw = coreFail

-- Traversable (specialised)
traverse' : (a -> Core b) -> List a -> List b -> Core (List b)
traverse' f [] acc = pure (reverse acc)
traverse' f (x :: xs) acc
    = traverse' f xs (!(f x) :: acc)

%inline
export
traverse : (a -> Core b) -> List a -> Core (List b)
traverse f xs = traverse' f xs []

%inline
export
for : List a -> (a -> Core b) -> Core (List b)
for = flip traverse

export
traverseList1 : (a -> Core b) -> List1 a -> Core (List1 b)
traverseList1 f xxs
    = let x = head xxs
          xs = tail xxs in
          [| f x ::: traverse f xs |]

export
traverseVect : (a -> Core b) -> Vect n a -> Core (Vect n b)
traverseVect f [] = pure []
traverseVect f (x :: xs) = [| f x :: traverseVect f xs |]

%inline
export
traverseOpt : (a -> Core b) -> Maybe a -> Core (Maybe b)
traverseOpt f Nothing = pure Nothing
traverseOpt f (Just x) = map Just (f x)

export
traversePair : (a -> Core b) -> (w, a) -> Core (w, b)
traversePair f (w, a) = (w,) <$> f a

export
traverse_ : (a -> Core b) -> List a -> Core ()
traverse_ f [] = pure ()
traverse_ f (x :: xs)
    = Core.do ignore (f x)
              traverse_ f xs

%inline
export
sequence : List (Core a) -> Core (List a)
sequence (x :: xs)
   = do
        x' <- x
        xs' <- sequence xs
        pure (x' :: xs')
sequence [] = pure []

export
traverseList1_ : (a -> Core b) -> List1 a -> Core ()
traverseList1_ f xxs
    = do let x = head xxs
         let xs = tail xxs
         ignore (f x)
         traverse_ f xs

namespace PiInfo
  export
  traverse : (a -> Core b) -> PiInfo a -> Core (PiInfo b)
  traverse f Explicit = pure Explicit
  traverse f Implicit = pure Implicit
  traverse f AutoImplicit = pure AutoImplicit
  traverse f (DefImplicit t) = pure (DefImplicit !(f t))

namespace Binder
  export
  traverse : (a -> Core b) -> Binder a -> Core (Binder b)
  traverse f (Lam fc c p ty) = pure $ Lam fc c !(traverse f p) !(f ty)
  traverse f (Let fc c val ty) = pure $ Let fc c !(f val) !(f ty)
  traverse f (Pi fc c p ty) = pure $ Pi fc c !(traverse f p) !(f ty)
  traverse f (PVar fc c p ty) = pure $ PVar fc c !(traverse f p) !(f ty)
  traverse f (PLet fc c val ty) = pure $ PLet fc c !(f val) !(f ty)
  traverse f (PVTy fc c ty) = pure $ PVTy fc c !(f ty)

export
mapTermM : ({vars : _} -> Term vars -> Core (Term vars)) ->
           ({vars : _} -> Term vars -> Core (Term vars))
mapTermM f = goTerm where

    goTerm : {vars : _} -> Term vars -> Core (Term vars)
    goTerm tm@(Local _ _ _ _) = f tm
    goTerm tm@(Ref _ _ _) = f tm
    goTerm (Meta fc n i args) = f =<< Meta fc n i <$> traverse goTerm args
    goTerm (Bind fc x bd sc) = f =<< Bind fc x <$> traverse goTerm bd <*> goTerm sc
    goTerm (App fc fn arg) = f =<< App fc <$> goTerm fn <*> goTerm arg
    goTerm (As fc u as pat) = f =<< As fc u <$> goTerm as <*> goTerm pat
    goTerm (TDelayed fc la d) = f =<< TDelayed fc la <$> goTerm d
    goTerm (TDelay fc la ty arg) = f =<< TDelay fc la <$> goTerm ty <*> goTerm arg
    goTerm (TForce fc la t) = f =<< TForce fc la <$> goTerm t
    goTerm tm@(PrimVal _ _) = f tm
    goTerm tm@(Erased _ _) = f tm
    goTerm tm@(TType _) = f tm


export
anyM : (a -> Core Bool) -> List a -> Core Bool
anyM f [] = pure False
anyM f (x :: xs)
    = if !(f x)
         then pure True
         else anyM f xs

export
allM : (a -> Core Bool) -> List a -> Core Bool
allM f [] = pure True
allM f (x :: xs)
    = if !(f x)
         then allM f xs
         else pure False

export
filterM : (a -> Core Bool) -> List a -> Core (List a)
filterM p [] = pure []
filterM p (x :: xs)
    = if !(p x)
         then do xs' <- filterM p xs
                 pure (x :: xs')
         else filterM p xs

export
data Ref : (l : label) -> Type -> Type where
     [search l]
     MkRef : IORef a -> Ref x a

export
newRef : (x : label) -> t -> Core (Ref x t)
newRef x val
    = do ref <- coreLift (newIORef val)
         pure (MkRef ref)

export %inline
get : (x : label) -> {auto ref : Ref x a} -> Core a
get x {ref = MkRef io} = coreLift (readIORef io)

export %inline
put : (x : label) -> {auto ref : Ref x a} -> a -> Core ()
put x {ref = MkRef io} val = coreLift (writeIORef io val)

export %inline
update : (x : label) -> {auto ref : Ref x a} -> (a -> a) -> Core ()
update x f
  = do v <- get x
       put x (f v)

export
wrapRef : (x : label) -> {auto ref : Ref x a} ->
          (a -> Core ()) ->
          Core b ->
          Core b
wrapRef x onClose op
  = do v <- get x
       o <- catch op $ \err =>
              do onClose v
                 put x v
                 throw err
       onClose v
       put x v
       pure o

export
cond : List (Lazy Bool, Lazy a) -> a -> a
cond [] def = def
cond ((x, y) :: xs) def = if x then y else cond xs def

export
condC : List (Core Bool, Core a) -> Core a -> Core a
condC [] def = def
condC ((x, y) :: xs) def
    = if !x then y else condC xs def
