module Idris.Package.Types

import Core.FC
import Core.Name.Namespace
import Data.Maybe
import Data.Strings
import Idris.CommandLine
import Idris.Version
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util

%default total

------------------------------------------------------------------------------
-- Versions

public export
data PkgVersion = MkPkgVersion (List1 Nat)

export
Show PkgVersion where
  show (MkPkgVersion vs) = showSep "." (map show (forget vs))

export
Pretty PkgVersion where
  pretty = pretty . show

export
Eq PkgVersion where
  MkPkgVersion p == MkPkgVersion q = p == q

export
Ord PkgVersion where
  -- list ordering gives us what we want
  compare (MkPkgVersion p) (MkPkgVersion q) = compare p q

------------------------------------------------------------------------------
-- Version Bounds

-- version must be >= lowerBound and <= upperBound
-- Do we want < and > as well?
public export
record PkgVersionBounds where
  constructor MkPkgVersionBounds
  lowerBound : Maybe PkgVersion
  lowerInclusive : Bool -- >= if true
  upperBound : Maybe PkgVersion
  upperInclusive : Bool -- <= if true

export
Show PkgVersionBounds where
  show p = if noBounds then "any" else lowerBounds ++ upperBounds

    where

      noBounds : Bool
      noBounds = isNothing p.lowerBound && isNothing p.upperBound

      lowerBounds : String
      lowerBounds = case p.lowerBound of
        Nothing => ""
        Just v  => (if p.lowerInclusive then ">= " else "> ") ++ show v ++ " "

      upperBounds : String
      upperBounds = case p.upperBound of
        Nothing => ""
        Just v  => (if p.upperInclusive then "<= " else "< ") ++ show v

export
anyBounds : PkgVersionBounds
anyBounds = MkPkgVersionBounds Nothing True Nothing True

export
current : PkgVersionBounds
current = let (maj,min,patch) = semVer version
              version = Just (MkPkgVersion (maj ::: [min, patch])) in
              MkPkgVersionBounds version True version True

export
inBounds : Maybe PkgVersion -> PkgVersionBounds -> Bool
inBounds mv bounds
   = let v = fromMaybe (MkPkgVersion (0 ::: [])) mv in
     maybe True (\v' => if bounds.lowerInclusive
                           then v >= v'
                           else v > v') bounds.lowerBound &&
     maybe True (\v' => if bounds.upperInclusive
                           then v <= v'
                           else v < v') bounds.upperBound

------------------------------------------------------------------------------
-- Dependencies

public export
record Depends where
  constructor MkDepends
  pkgname : String
  pkgbounds : PkgVersionBounds

export
Show Depends where
  show p = p.pkgname ++ " " ++ show p.pkgbounds

export
Pretty Depends where
  pretty = pretty . show

------------------------------------------------------------------------------
-- Package description

public export
record PkgDesc where
  constructor MkPkgDesc
  name : String
  version : Maybe PkgVersion
  authors : Maybe String
  maintainers : Maybe String
  license : Maybe String
  brief   : Maybe String
  readme  : Maybe String
  homepage : Maybe String
  sourceloc : Maybe String
  bugtracker : Maybe String
  depends : List Depends -- packages to add to search path
  modules : List (ModuleIdent, String) -- modules to install (namespace, filename)
  mainmod : Maybe (ModuleIdent, String) -- main file (i.e. file to load at REPL)
  executable : Maybe String -- name of executable
  options : Maybe (FC, String)
  sourcedir : Maybe String
  builddir : Maybe String
  outputdir : Maybe String
  prebuild : Maybe (FC, String) -- Script to run before building
  postbuild : Maybe (FC, String) -- Script to run after building
  preinstall : Maybe (FC, String) -- Script to run after building, before installing
  postinstall : Maybe (FC, String) -- Script to run after installing
  preclean : Maybe (FC, String) -- Script to run before cleaning
  postclean : Maybe (FC, String) -- Script to run after cleaning

export
initPkgDesc : String -> PkgDesc
initPkgDesc pname
    = MkPkgDesc pname Nothing Nothing Nothing Nothing
                Nothing Nothing Nothing Nothing Nothing
                [] []
                Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing
                Nothing Nothing Nothing Nothing

export
Show PkgDesc where
  show pkg = "Package: " ++ name pkg ++ "\n" ++
             maybe "" (\m => "Version: "     ++ m ++ "\n") (show <$> version pkg) ++
             maybe "" (\m => "Authors: "     ++ m ++ "\n") (authors pkg)     ++
             maybe "" (\m => "Maintainers: " ++ m ++ "\n") (maintainers pkg) ++
             maybe "" (\m => "License: "     ++ m ++ "\n") (license pkg)     ++
             maybe "" (\m => "Brief: "       ++ m ++ "\n") (brief pkg)       ++
             maybe "" (\m => "ReadMe: "      ++ m ++ "\n") (readme pkg)      ++
             maybe "" (\m => "HomePage: "    ++ m ++ "\n") (homepage pkg)    ++
             maybe "" (\m => "SourceLoc: "   ++ m ++ "\n") (sourceloc pkg)   ++
             maybe "" (\m => "BugTracker: "  ++ m ++ "\n") (bugtracker pkg)  ++
             "Depends: " ++ show (depends pkg) ++ "\n" ++
             "Modules: " ++ show (map snd (modules pkg)) ++ "\n" ++
             maybe "" (\m => "Main: " ++ snd m ++ "\n") (mainmod pkg) ++
             maybe "" (\m => "Exec: " ++ m ++ "\n") (executable pkg) ++
             maybe "" (\m => "Opts: " ++ snd m ++ "\n") (options pkg) ++
             maybe "" (\m => "SourceDir: " ++ m ++ "\n") (sourcedir pkg) ++
             maybe "" (\m => "BuildDir: " ++ m ++ "\n") (builddir pkg) ++
             maybe "" (\m => "OutputDir: " ++ m ++ "\n") (outputdir pkg) ++
             maybe "" (\m => "Prebuild: " ++ snd m ++ "\n") (prebuild pkg) ++
             maybe "" (\m => "Postbuild: " ++ snd m ++ "\n") (postbuild pkg) ++
             maybe "" (\m => "Preinstall: " ++ snd m ++ "\n") (preinstall pkg) ++
             maybe "" (\m => "Postinstall: " ++ snd m ++ "\n") (postinstall pkg) ++
             maybe "" (\m => "Preclean: " ++ snd m ++ "\n") (preclean pkg) ++
             maybe "" (\m => "Postclean: " ++ snd m ++ "\n") (postclean pkg)

export
Pretty PkgDesc where
  pretty desc = vcat
    [ field  "name"        desc.name
    , mfield "version"     desc.version
    , mfield "authors"     desc.authors
    , mfield "maintainers" desc.maintainers
    , mfield "license"     desc.license
    , mfield "brief"       desc.brief
    , mfield "readme"      desc.readme
    , mfield "homepage"    desc.homepage
    , mfield "sourceloc"   desc.sourceloc
    , mfield "bugtracker"  desc.bugtracker
    , lfield "depends"     desc.depends
    , lfield "modules"     (fst <$> desc.modules)
--   mainmod : Maybe (ModuleIdent, String) -- main file (i.e. file to load at REPL)
    , mfield "executable"  desc.executable
    , mfield "options"     (show . snd <$> desc.options)
    , mfield "sourcedir"   desc.sourcedir
    , mfield "builddir"    desc.builddir
    , mfield "outputdir"   desc.outputdir
    , mfield "prebuild"    (snd <$> desc.prebuild)
    , mfield "postbuild"   (snd <$> desc.postbuild)
    , mfield "preinstall"  (snd <$> desc.preinstall)
    , mfield "postinstall" (snd <$> desc.postinstall)
    , mfield "preclean"    (snd <$> desc.preclean)
    , mfield "postclean"   (snd <$> desc.postclean)
    ]

  where
    field : Pretty a => String -> a -> Doc ann
    field nm val = hsep [ pretty nm, equals, pretty val ]

    mfield : Pretty a => String -> Maybe a -> Doc ann
    mfield nm Nothing = hsep [ pretty "--", pretty nm, equals ]
    mfield nm (Just val) = field nm val

    lfield : Pretty a => String -> List a -> Doc ann
    lfield nm [] = hsep [ pretty "--", pretty nm, equals ]
    lfield nm xs = pretty nm
               <++> equals
               <++> align (sep (punctuate comma (map pretty xs)))
