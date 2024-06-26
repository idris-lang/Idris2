{ stdenv, lib, overrideSDK, gmp, idris2Version }:
let
  stdenv' = if stdenv.isDarwin then overrideSDK stdenv "11.0" else stdenv;
in
stdenv'.mkDerivation rec {
  pname = "libidris2_support";
  version = idris2Version;

  # we don't rebuild Idris when changing the buildIdris nix
  # function:
  src = with lib.fileset; toSource {
    root = ../.;
    fileset = difference ../. ../nix/buildIdris.nix;
  };

  strictDeps = true;
  buildInputs = [ gmp ];

  makeFlags = [
    "PREFIX=$(out)"
  ] ++ lib.optional stdenv'.isDarwin "OS=";

  buildFlags = [ "support" ];

  installTargets = "install-support";

  postInstall = ''
    mv $out/idris2-${version}/lib $out/lib
    mv $out/idris2-${version}/support $out/share
    rmdir $out/idris2-${version}
  '';
}
