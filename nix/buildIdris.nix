{ stdenv
, projectName
, src
, idris2
}:

stdenv.mkDerivation {
  name = projectName;
  src = src;
  buildInputs = [ idris2 ];
  buildPhase = let
    ipkgName = projectName + ".ipkg";
  in ''
    idris2 --build ${ipkgName}
  '';
  installPhase = ''
    mkdir -p $out/
    mv build/exec/* $out
  '';
}
