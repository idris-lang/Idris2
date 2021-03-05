{ stdenv
, projectName
, src
, idris2
, idris2-version
}:

let
  ipkgName = projectName + ".ipkg";
in
rec {
  build = stdenv.mkDerivation {
    name = projectName;
    src = src;
    buildInputs = [ idris2 ];
    buildPhase = let
    in ''
      idris2 --build ${ipkgName}
    '';
    installPhase = ''
      mkdir -p $out/bin
      mv build/exec/* $out/bin
    '';
  };
  installLibrary = build.overrideAttrs (oldAttrs: {
    installPhase = let
      ipkgName = projectName + ".ipkg";
      idrName = "idris2-${idris2-version}";
    in ''
      mkdir -p $out/lib/${idrName}
      export IDRIS2_PREFIX=$out/lib
      idris2 --install ${ipkgName}
    '';
  });
}
