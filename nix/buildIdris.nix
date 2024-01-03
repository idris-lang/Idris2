{ stdenv, lib, idris2-version, idris2 }:
{ src, projectName, idrisLibraries, ... }@attrs:

let
  ipkgName = projectName + ".ipkg";
  idrName = "idris2-${idris2-version}";
  libSuffix = "lib/${idrName}";
  lib-dirs =
    lib.strings.makeSearchPath libSuffix idrisLibraries;
  drvAttrs = builtins.removeAttrs attrs [ "idrisLibraries" ];
in rec {
  executable = stdenv.mkDerivation (drvAttrs // {
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
  library = { withSource ? false }:
    let installCmd = if withSource then "--install-with-src" else "--install";
    in executable.overrideAttrs (_: {
      installPhase = ''
        runHook preInstall
        mkdir -p $out/${libSuffix}
        export IDRIS2_PREFIX=$out/lib
        idris2 ${installCmd} ${ipkgName}
        runHook postInstall
      '';
    });
  # deprecated aliases:
  build = lib.warn "build is a deprecated alias for 'executable'." executable;
  installLibrary = lib.warn "installLibrary is a deprecated alias for 'library { }'." (library { });
}
