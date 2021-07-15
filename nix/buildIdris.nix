{ stdenv
, lib
, projectName
, src
, idris2
, idris2-version
, idrisLibraries
}:

let
  ipkgName = projectName + ".ipkg";
  idrName = "idris2-${idris2-version}";
  libSuffix = "lib/${idrName}";
  lib-dirs = lib.strings.concatMapStringsSep ":" (p: "${p}/${libSuffix}") idrisLibraries;
in
rec {
  build = stdenv.mkDerivation {
    name = projectName;
    src = src;
    nativeBuildInputs = [ idris2 ];
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
  installLibrary = build.overrideAttrs (_: {
    buildPhase = "";
    installPhase = ''
      mkdir -p $out/${libSuffix}
      export IDRIS2_PREFIX=$out/lib
      idris2 --install ${ipkgName}
    '';
  });
}
