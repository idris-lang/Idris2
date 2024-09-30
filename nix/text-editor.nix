{ pkgs, idris-emacs-src, idris2Pkg }:
with pkgs;
let
  init-file = ./init.el;
  makeEmacsWrapper = name: my-emacs: init:
    writeShellScriptBin name ''
      ${my-emacs}/bin/emacs -q -l ${init-file} $@
    '';
in rec {
  idris2-mode = emacsPackages.trivialBuild {
    pname = "idris2-mode";
    src = idris-emacs-src;
    packageRequires = with pkgs.emacsPackages.melpaPackages; [ prop-menu ];
    version = "1";
    recipe = pkgs.writeText "recipe" ''
      (idris2-mode :repo "redfish64/idris2-mode" :fetcher github)
    '';
  };
  idris-emacs = emacsWithPackages [ idris2-mode ];
  emacs-dev = makeEmacsWrapper "emacs-dev" idris-emacs init-file;
  emacs-with-idris = writeShellScriptBin "emacs-with-idris" ''
    export PATH=${idris2Pkg}/bin:$PATH
    ${emacs-dev}/bin/emacs-dev $@
  '';
}
