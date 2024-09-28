{ idris2Version, shortRev ? null }:
final: prev:
let
  chezSupportsSystem = (prev.system == "x86_64-linux")
    || (prev.lib.versionAtLeast prev.chez.version "10.0.0");
  chez = if chezSupportsSystem then prev.chez else prev.chez-racket;
  idris2Bootstrap = prev.callPackage ./package.nix {
    inherit chez idris2Version;
    inherit (final.idris2Packages) support;
    idris2Bootstrap = null;
    srcRev = if shortRev == null then "dirty" else shortRev;
  };
in
{
  idris2Packages = prev.idris2Packages // {
    support = prev.callPackage ./support.nix { inherit idris2Version; };
    idris2 = prev.callPackage ./package.nix {
      inherit chez idris2Bootstrap idris2Version;
      inherit (final.idris2Packages) support;
      srcRev = if shortRev == null then "dirty" else shortRev;
    };
    buildIdris = final.callPackage ./buildIdris.nix { inherit idris2Version; };
    idris2Api = final.callPackage ./idris2Api.nix { inherit idris2Version; };
  };
  idris2 = final.idris2Packages.idris2;
}
