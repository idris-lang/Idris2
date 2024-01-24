{ stdenv, lib, gmp, idris2Version }:
stdenv.mkDerivation rec {
  pname = "libidris2_support";
  version = idris2Version;

  src = ../.;

  strictDeps = true;
  buildInputs = [ gmp ];

  makeFlags = [
    "PREFIX=$(out)"
  ] ++ lib.optional stdenv.isDarwin "OS=";

  buildFlags = [ "support" ];

  installTargets = "install-support";

  postInstall = ''
    mv $out/idris2-${version}/lib $out/lib
    mv $out/idris2-${version}/support $out/share
    rmdir $out/idris2-${version}
  '';
}
