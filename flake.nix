{
  description = "Idris2 flake";

  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.idris-emacs-src = {
    url = github:redfish64/idris2-mode;
    flake = false;
  };

  outputs = { self, nixpkgs, flake-utils, idris-emacs-src }: flake-utils.lib.eachDefaultSystem (system:
    let pkgs = import nixpkgs { inherit system; };
        text-editor = import ./nix/text-editor.nix { inherit pkgs idris-emacs-src; };
    in rec {
      packages = rec {
        idris2 = import ./default.nix { inherit pkgs; };
        buildIdris = { projectName, src }:
          import ./nix/buildIdris.nix { inherit idris2 src projectName; stdenv = pkgs.stdenv; };
      } // text-editor;
      apps = rec {
        type = "app";
        emacs-dev = text-editor.emacs-dev;
      };
      defaultPackage = packages.idris2;
    }) // rec {
      templates.pkg = {
          path = ./nix/templates/pkg;
          description = "A custom Idris 2 package";
      };
      defaultTemplate = templates.pkg;
    };
}
