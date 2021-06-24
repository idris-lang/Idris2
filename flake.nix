{
  description = "Idris2 flake";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.idris-emacs-src = {
    url = "github:redfish64/idris2-mode";
    flake = false;
  };

  outputs = { self, nixpkgs, flake-utils, idris-emacs-src }:
    let
      idris2-version = "0.4.0";
      lib = import ./nix/lib.nix;
      sys-agnostic = rec {
        templates.pkg = {
          path = ./nix/templates/pkg;
          description = "A custom Idris 2 package";
        };
        templates.pkgWithDeps = {
          path = ./nix/templates/pkgWithDeps;
          description = "A custom Idris 2 package with dependencies";
        };
        defaultTemplate = templates.pkg;
        version = idris2-version;
      };
      per-system = { config ? { }, overlays ? [ ] }: system:
        let
          pkgs = import nixpkgs { inherit config system overlays; };
          idris2Pkg = pkgs.callPackage ./nix/package.nix {
            inherit idris2-version;
            srcRev = self.shortRev or "dirty";
          };
          buildIdris = { projectName, src, idrisLibraries }:
            pkgs.callPackage ./nix/buildIdris.nix
              { inherit src projectName idrisLibraries idris2-version; idris2 = idris2Pkg; };
        in
        if system != "aarch64-linux" then rec {
          checks = import ./nix/test.nix {
            inherit (pkgs) system stdenv runCommand lib;
            inherit nixpkgs flake-utils;
            idris = self;
          };
          packages =
            { idris2 = idris2Pkg; }
            // (import ./nix/text-editor.nix { inherit pkgs idris-emacs-src idris2Pkg; });
          inherit buildIdris;
          defaultPackage = packages.idris2;
        } else { };
    in
    lib.mkOvrOptsFlake (opts: flake-utils.lib.eachDefaultSystem (per-system opts) // sys-agnostic);
}
