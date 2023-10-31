module Core.TT.Directive

import Core.FC
import Core.Name
import Core.TT.Term

import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util

------------------------------------------------------------------------
-- Types

public export
data Visibility = Private | Export | Public
%name Visibility vis

public export
data TotalReq = Total | CoveringOnly | PartialOK
%name TotalReq treq

public export
data PartialReason
  = NotStrictlyPositive
  | BadCall (List Name)
  -- sequence of mutually-recursive function calls leading to a non-terminating function
  | BadPath (List (FC, Name)) Name
  | RecPath (List (FC, Name))
%name PartialReason preas

public export
data Terminating
       = Unchecked
       | IsTerminating
       | NotTerminating PartialReason
%name Terminating ter

public export
data Covering
       = IsCovering
       | MissingCases (List ClosedTerm)
       | NonCoveringCall (List Name)
%name Covering cov

-- Totality status of a definition. We separate termination checking from
-- coverage checking.
public export
record Totality where
     constructor MkTotality
     isTerminating : Terminating
     isCovering : Covering
%name Totality tot

------------------------------------------------------------------------
-- Smart constructors

export
unchecked : Totality
unchecked = MkTotality Unchecked IsCovering

export
isTotal : Totality
isTotal = MkTotality Unchecked IsCovering

export
notCovering : Totality
notCovering = MkTotality Unchecked (MissingCases [])

------------------------------------------------------------------------
-- Instances for Visibility

export
Show Visibility where
  show Private = "private"
  show Export = "export"
  show Public = "public export"

export
Pretty Void Visibility where
  pretty Private = pretty "private"
  pretty Export = pretty "export"
  pretty Public = pretty "public" <++> pretty "export"

export
Eq Visibility where
  Private == Private = True
  Export == Export = True
  Public == Public = True
  _ == _ = False

export
Ord Visibility where
  compare Private Export = LT
  compare Private Public = LT
  compare Export Public = LT

  compare Private Private = EQ
  compare Export Export = EQ
  compare Public Public = EQ

  compare Export Private = GT
  compare Public Private = GT
  compare Public Export = GT

------------------------------------------------------------------------
-- Instances for TotalReq

export
Show TotalReq where
    show Total = "total"
    show CoveringOnly = "covering"
    show PartialOK = "partial"

export
Pretty Void TotalReq where
  pretty = pretty . show

export
Eq TotalReq where
    (==) Total Total = True
    (==) CoveringOnly CoveringOnly = True
    (==) PartialOK PartialOK = True
    (==) _ _ = False

||| Bigger means more requirements
||| So if a definition was checked at b, it can be accepted at a <= b.
export
Ord TotalReq where
  PartialOK <= _ = True
  _ <= Total = True
  a <= b = a == b

  a < b = a <= b && a /= b

------------------------------------------------------------------------
-- Instances for PartialReason

export
Show PartialReason where
  show NotStrictlyPositive = "not strictly positive"
  show (BadCall [n])
      = "possibly not terminating due to call to " ++ show n
  show (BadCall ns)
      = "possibly not terminating due to calls to " ++ showSep ", " (map show ns)
  show (BadPath [_] n)
      = "possibly not terminating due to call  to " ++ show n
  show (BadPath init n)
      = "possibly not terminating due to function " ++ show n ++ " being reachable via " ++ showSep " -> " (map show init)
  show (RecPath loop)
      = "possibly not terminating due to recursive path " ++ showSep " -> " (map (show . snd) loop)

export
Pretty Void PartialReason where
  pretty NotStrictlyPositive = reflow "not strictly positive"
  pretty (BadCall [n])
    = reflow "possibly not terminating due to call to" <++> pretty n
  pretty (BadCall ns)
    = reflow "possibly not terminating due to calls to" <++> concatWith (surround (comma <+> space)) (pretty <$> ns)
  pretty (BadPath [_] n)
    = reflow "possibly not terminating due to call to" <++> pretty n
  pretty (BadPath init n)
    = reflow "possibly not terminating due to function" <++> pretty n
      <++> reflow "being reachable via"
      <++> concatWith (surround (pretty " -> ")) (pretty <$> map snd init)
  pretty (RecPath loop)
    = reflow "possibly not terminating due to recursive path" <++> concatWith (surround (pretty " -> ")) (pretty <$> map snd loop)

------------------------------------------------------------------------
-- Instances for Terminating

export
Show Terminating where
  show Unchecked = "not yet checked"
  show IsTerminating = "terminating"
  show (NotTerminating p) = show p

export
Pretty Void Terminating where
  pretty Unchecked = reflow "not yet checked"
  pretty IsTerminating = pretty "terminating"
  pretty (NotTerminating p) = pretty p

------------------------------------------------------------------------
-- Instances for Covering

export
Show Covering where
  show IsCovering = "covering"
  show (MissingCases c) = "not covering all cases"
  show (NonCoveringCall [f])
     = "not covering due to call to function " ++ show f
  show (NonCoveringCall cs)
     = "not covering due to calls to functions " ++ showSep ", " (map show cs)

export
Pretty Void Covering where
  pretty IsCovering = pretty "covering"
  pretty (MissingCases c) = reflow "not covering all cases"
  pretty (NonCoveringCall [f])
     = reflow "not covering due to call to function" <++> pretty f
  pretty (NonCoveringCall cs)
     = reflow "not covering due to calls to functions" <++> concatWith (surround (comma <+> space)) (pretty <$> cs)

------------------------------------------------------------------------
-- Instances for Totality

export
Show Totality where
  show tot
    = let t = isTerminating tot
          c = isCovering tot in
        showTot t c
    where
      showTot : Terminating -> Covering -> String
      showTot IsTerminating IsCovering = "total"
      showTot IsTerminating c = show c
      showTot t IsCovering = show t
      showTot t c = show c ++ "; " ++ show t

export
Pretty Void Totality where
  pretty (MkTotality IsTerminating IsCovering) = pretty "total"
  pretty (MkTotality IsTerminating c) = pretty c
  pretty (MkTotality t IsCovering) = pretty t
  pretty (MkTotality t c) = pretty c <+> semi <++> pretty t
