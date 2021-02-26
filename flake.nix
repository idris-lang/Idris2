{
  description = "Idris2 flake";

  inputs.flake-utils.url = github:numtide/flake-utils;

  outputs = { self, nixpkgs, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
    let pkgs = import nixpkgs { inherit system; };
    in rec {
      packages = rec {
        idris2 = import ./default.nix { inherit pkgs; };
        buildIdris = { projectName, src }:
          import ./nix/buildIdris.nix { inherit idris2 src projectName; stdenv = pkgs.stdenv; };
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
