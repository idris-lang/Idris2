module Idris.Package.ToJson

import Idris.Package.Types
import Libraries.Data.String.Extra
import Data.List
import Core.FC
import Core.Name.Namespace

%hide Syntax.PreorderReasoning.Generic.infixl.(~=)
%hide Syntax.PreorderReasoning.infixl.(~=)

-- We don't bother with a robust JSON implementation
-- for this one-off JSON serialization.

infix 0 ~=, ~~=

interface ToJson v where
  toJson : v -> String

ToJson String where
  toJson str = "\"\{str}\""

(~=) : ToJson v => String -> v -> String
(~=) field value = "\{toJson field}: \{toJson value}"

(~~=) : ToJson v => String -> Maybe v -> Maybe String
(~~=) field = map (field ~=)

ToJson PkgVersion where
  toJson v = "\"\{show v}\""

ToJson Bool where
  toJson False = "false"
  toJson True = "true"

ToJson a => ToJson (List a) where
  toJson xs = "[\{join "," $ map toJson xs}]"

ToJson PkgVersionBounds where
  toJson (MkPkgVersionBounds lowerBound lowerInclusive upperBound upperInclusive) =
    let optionalFields = catMaybes [
          "lowerBound" ~~= lowerBound
        , "upperBound" ~~= upperBound
        ]
        fields = [
          "lowerInclusive" ~= lowerInclusive
        , "upperInclusive" ~= upperInclusive
        ] ++ optionalFields
    in
      "{\{join "," fields}}"

ToJson Depends where
  toJson d = "\"\{show d}\""

ToJson (ModuleIdent, String) where
  toJson (ident, n) = "\"\{show ident}\""

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
      let optionalFields = catMaybes [
            "version" ~~= version
          , "langversion" ~~= langversion
          , "authors" ~~= authors
          , "maintainers" ~~= maintainers
          , "license" ~~= license
          , "brief" ~~= brief
          , "readme" ~~= readme
          , "homepage" ~~= homepage
          , "sourceloc" ~~= sourceloc
          , "bugtracker" ~~= bugtracker
          , "main" ~~= mainmod
          , "executable" ~~= executable
          , "opts" ~~= snd <$> options
          , "sourcedir" ~~= sourcedir
          , "builddir" ~~= builddir
          , "outputdir" ~~= outputdir
          , "prebuild" ~~= snd <$> prebuild
          , "postbuild" ~~= snd <$> postbuild
          , "preinstall" ~~= snd <$> preinstall
          , "postinstall" ~~= snd <$> postinstall
          , "preclean" ~~= snd <$> preclean
          , "postclean" ~~= snd <$> postclean
          ]
          fields = [
            "name" ~= name
          , "depends" ~= depends
          , "modules" ~= modules
          ] ++ optionalFields
      in
        "{\{join "," fields}}"

