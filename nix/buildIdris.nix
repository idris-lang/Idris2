{ stdenv
, lib
, idris2-version
, idris2
}:
{
src
, projectName
, idrisLibraries
, ...
}@attrs:

let
  ipkgName = projectName + ".ipkg";
  idrName = "idris2-${idris2-version}";
  libSuffix = "lib/${idrName}";
  lib-dirs = lib.strings.concatMapStringsSep ":" (p: "${p}/${libSuffix}") idrisLibraries;
  drvAttrs = builtins.removeAttrs attrs [ "idrisLibraries" ];
in
rec {
  build = stdenv.mkDerivation (drvAttrs // {
    name = projectName;
    src = src;
    nativeBuildInputs = [ idris2 ];
    configurePhase = ''
      runHook preConfigure
      export IDRIS2_PACKAGE_PATH=${lib-dirs}
      runHook postConfigure
    '';
    buildPhase = ''
      runHook preBuild
      idris2 --build ${ipkgName}
      runHook postBuild
    '';
    installPhase = ''
      runHook preInstall
      mkdir -p $out/bin
      mv build/exec/* $out/bin
      runHook postInstall
    '';
  });
  installLibrary = build.overrideAttrs (_: {
    buildPhase = "";
    installPhase = ''
      mkdir -p $out/${libSuffix}
      export IDRIS2_PREFIX=$out/lib
      idris2 --install ${ipkgName}
    '';
  });
}
