module Idris.Syntax.Pragmas

import Data.List -- until 0.6.0 release
import Data.String

%default total

public export
data KwPragma
  = KwHide
  | KwUnhide
  | KwLogging
  | KwAutoLazy
  | KwUnboundImplicits
  | KwAmbiguityDepth
  | KwPair
  | KwRewrite
  | KwIntegerLit
  | KwStringLit
  | KwCharLit
  | KwDoubleLit
  | KwName
  | KwStart
  | KwAllowOverloads
  | KwLanguage
  | KwDefault
  | KwPrefixRecordProjections
  | KwAutoImplicitDepth
  | KwNfMetavarThreshold
  | KwSearchTimeOut

public export
data LangExt
  = ElabReflection
  | Borrowing -- not yet implemented

export
allLangExts : List LangExt
allLangExts = [ElabReflection, Borrowing]

export
Show LangExt where
  show ElabReflection = "ElabReflection"
  show Borrowing = "Borrowing"

export
Eq LangExt where
  ElabReflection == ElabReflection = True
  Borrowing == Borrowing = True
  _ == _ = False

public export
data PragmaArg
  = AName String
  | ANameList
  | APairArg
  | ARewriteArg
  | AnOnOff
  | AnOptionalLoggingTopic
  | ANat
  | AnExpr
  | ALangExt
  | ATotalityLevel

export
Show PragmaArg where
  show (AName str) = str
  show ANameList = "nm xs f"
  show APairArg = "ty fst snd"
  show ARewriteArg = "eq rew"
  show AnOnOff = "on|off"
  show AnOptionalLoggingTopic = "[topic]"
  show ANat = "nat"
  show AnExpr = "expr"
  show ALangExt = concat $ intersperse "|" $ map show allLangExts
  show ATotalityLevel = "partial|total|covering"

export
pragmaArgs : KwPragma -> List PragmaArg
pragmaArgs KwHide = [AName "nm"]
pragmaArgs KwUnhide = [AName "nm"]
pragmaArgs KwLogging = [AnOptionalLoggingTopic, ANat]
pragmaArgs KwAutoLazy = [AnOnOff]
pragmaArgs KwUnboundImplicits = [AnOnOff]
pragmaArgs KwAmbiguityDepth = [ANat]
pragmaArgs KwPair = [APairArg]
pragmaArgs KwRewrite = [ARewriteArg]
pragmaArgs KwIntegerLit = [AName "nm"]
pragmaArgs KwStringLit = [AName "nm"]
pragmaArgs KwCharLit = [AName "nm"]
pragmaArgs KwDoubleLit = [AName "nm"]
pragmaArgs KwName = [ANameList]
pragmaArgs KwStart = [AnExpr]
pragmaArgs KwAllowOverloads = [AName "nm"]
pragmaArgs KwLanguage = [ALangExt]
pragmaArgs KwDefault = [ATotalityLevel]
pragmaArgs KwPrefixRecordProjections = [AnOnOff]
pragmaArgs KwAutoImplicitDepth = [ANat]
pragmaArgs KwNfMetavarThreshold = [ANat]
pragmaArgs KwSearchTimeOut = [ANat]

export
Show KwPragma where
  show kw = case kw of
    KwHide => "%hide"
    KwUnhide => "%unhide"
    KwLogging => "%logging"
    KwAutoLazy => "%auto_lazy"
    KwUnboundImplicits => "%unbound_implicits"
    KwAmbiguityDepth => "%ambiguity_depth"
    KwPair => "%pair"
    KwRewrite => "%rewrite"
    KwIntegerLit => "%integerLit"
    KwStringLit => "%stringLit"
    KwCharLit => "%charLit"
    KwDoubleLit => "%doubleLit"
    KwName => "%name"
    KwStart => "%start"
    KwAllowOverloads => "%allow_overloads"
    KwLanguage => "%language"
    KwDefault => "%default"
    KwPrefixRecordProjections => "%prefix_record_projections"
    KwAutoImplicitDepth => "%auto-implicit_depth"
    KwNfMetavarThreshold => "%metavar_threshold"
    KwSearchTimeOut => "%search_timeout"

export
allPragmas : List KwPragma
allPragmas =
  [ KwHide
  , KwUnhide
  , KwLogging
  , KwAutoLazy
  , KwUnboundImplicits
  , KwAmbiguityDepth
  , KwPair
  , KwRewrite
  , KwIntegerLit
  , KwStringLit
  , KwCharLit
  , KwDoubleLit
  , KwName
  , KwStart
  , KwAllowOverloads
  , KwLanguage
  , KwDefault
  , KwPrefixRecordProjections
  , KwAutoImplicitDepth
  , KwNfMetavarThreshold
  , KwSearchTimeOut
  ]

export
pragmaTopics : String
pragmaTopics
  = concat $ intersperse "\n" $ map ("+ " ++)
  $ map (\ kw => unwords (show kw :: map show (pragmaArgs kw)))
  $ allPragmas
