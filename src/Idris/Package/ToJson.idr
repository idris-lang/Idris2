module Idris.Package.ToJson

import Idris.Package.Types
import Libraries.Data.String.Extra
import Data.List
import Core.FC
import Core.Name.Namespace
import Data.Maybe

%default total

-- We don't bother with a robust JSON implementation
-- for this one-off JSON serialization.

private infixl 0 ~~=

interface ToJson v where
  toJson : v -> String

ToJson String where
  toJson str = "\"\{str}\""

ToJson Bool where
  toJson False = "false"
  toJson True = "true"

ToJson a => ToJson (List a) where
  toJson xs = "[\{join "," $ map toJson xs}]"

(~=) : ToJson v => String -> v -> String
(~=) field value = "\{toJson field}: \{toJson value}"

(~~=) : ToJson v => String -> Maybe v -> Maybe String
(~~=) field = map (field ~=)

ToJson PkgVersion where
  toJson v = "\"\{show v}\""

ToJson PkgVersionBounds where
  toJson (MkPkgVersionBounds lowerBound lowerInclusive upperBound upperInclusive) =
    let fields =
        [ "lowerInclusive" ~= lowerInclusive
        , "lowerBound"     ~= maybe "*" show lowerBound
        , "upperInclusive" ~= upperInclusive
        , "upperBound"     ~= maybe "*" show upperBound
        ]
    in
      "{\{join "," fields}}"

ToJson Depends where
  toJson (MkDepends pkgname pkgbounds) = "{\{pkgname ~= pkgbounds}}"

ToJson ModuleIdent where
  toJson ident = "\"\{show ident}\""

namespace Package
  export
  toJson : PkgDesc -> String
  toJson (MkPkgDesc
            name
            version
            langversion
            authors
            maintainers
            license
            brief
            readme
            homepage
            sourceloc
            bugtracker
            depends
            modules
            mainmod
            executable
            options
            sourcedir
            builddir
            outputdir
            prebuild
            postbuild
            preinstall
            postinstall
            preclean
            postclean) =
    let optionalFields = catMaybes $
          [ "version"     ~~= version
          , "langversion" ~~= langversion
          , "authors"     ~~= authors
          , "maintainers" ~~= maintainers
          , "license"     ~~= license
          , "brief"       ~~= brief
          , "readme"      ~~= readme
          , "homepage"    ~~= homepage
          , "sourceloc"   ~~= sourceloc
          , "bugtracker"  ~~= bugtracker
          , "main"        ~~= fst <$> mainmod
          , "executable"  ~~= executable
          , "opts"        ~~= snd <$> options
          , "sourcedir"   ~~= sourcedir
          , "builddir"    ~~= builddir
          , "outputdir"   ~~= outputdir
          , "prebuild"    ~~= snd <$> prebuild
          , "postbuild"   ~~= snd <$> postbuild
          , "preinstall"  ~~= snd <$> preinstall
          , "postinstall" ~~= snd <$> postinstall
          , "preclean"    ~~= snd <$> preclean
          , "postclean"   ~~= snd <$> postclean
          ]
        fields =
          [ "name"    ~= name
          , "depends" ~= depends
          , "modules" ~= fst <$> modules
          ] ++ optionalFields
    in
      "{\{join "," fields}}"

