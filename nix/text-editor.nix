{ pkgs
, idris-emacs-src
}: with pkgs;
let
  makeEmacsWrapper = name: idris: writeShellScriptBin name ''
    ${idris}/bin/emacs --eval "(progn (require 'idris2-mode))" $@
  '';
in rec {
  idris2-mode = emacsPackages.melpaBuild {
    pname = "idris2-mode";
    src = idris-emacs-src;
    packageRequires = with pkgs.emacsPackages.melpaPackages; [ prop-menu ];
    version = "1";
    recipe = pkgs.writeText "recipe" ''
      (idris2-mode :repo "redfish64/idris2-mode" :fetcher github)
    '';
  };
  idris-emacs = emacsWithPackages [ idris2-mode ];
  emacs-dev = makeEmacsWrapper "emacs-dev" idris-emacs;
}
