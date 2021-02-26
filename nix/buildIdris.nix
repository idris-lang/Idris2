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
    ipkgName = projectName + ".idr";
  in ''
    idris2 ${ipkgName} -o ${projectName}
  # '';
  installPhase = ''
    mkdir -p $out/
    mv build/exec/* $out
  '';
}
