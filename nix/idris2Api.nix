{ idris2Packages, idris2Version }:
idris2Packages.buildIdris {
  src = ./..;
  ipkgName = "idris2api";
  version = idris2Version;
  idrisLibraries = [ ];
  preBuild = ''
    export IDRIS2_PREFIX=$out/lib
    make src/IdrisPaths.idr
  '';
}
