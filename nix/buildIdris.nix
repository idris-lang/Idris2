{ stdenv
, lib
, projectName
, src
, idris2
, idris2-version
, idrisLibraries
}:
with lib.strings;
let
  ipkgName = projectName + ".ipkg";
  libSuffix = "lib/${idrName}";
  idrName = "idris2-${idris2-version}";
  lib-dirs = concatMapStringsSep ":" (p: "${p}/${libSuffix}") idrisLibraries;
in
rec {
  build = stdenv.mkDerivation {
    name = projectName;
    src = src;
    buildInputs = [ idris2 ];
    configurePhase = ''
      export IDRIS2_PACKAGE_PATH=${lib-dirs}
    '';
    buildPhase = ''
      idris2 --build ${ipkgName}
    '';
    installPhase = ''
      mkdir -p $out/bin
      mv build/exec/* $out/bin
    '';
  };
  installLibrary = build.overrideAttrs (oldAttrs: {
    buildPhase = "";
    installPhase = let
      ipkgName = projectName + ".ipkg";
    in ''
      mkdir -p $out/${libSuffix}
      export IDRIS2_PREFIX=$out/lib
      idris2 --install ${ipkgName}
    '';
  });
}
