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
    mv build/exec $out
    mv $out && mv ${projectName} bin
  '';
}
