{
  description = "Idris2 flake";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.idris-emacs-src = {
    url = "github:redfish64/idris2-mode";
    flake = false;
  };
  inputs.nixpkgs.url = "github:NixOS/nixpkgs";

  outputs = { self, nixpkgs, flake-utils, idris-emacs-src }:
    let
      idris2Version = "0.7.0";
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
        overlays.default = import ./nix/overlay.nix {
          inherit idris2Version;
          shortRev = self.shortRev or null;
        };
        version = idris2Version;
      };
      per-system = { config ? { }, overlays ? [ ] }:
        system:
        let
          pkgs = import nixpkgs {
            inherit config system;
            overlays = overlays ++ [ self.overlays.default ];
          };
          stdenv' = with pkgs; if stdenv.isDarwin then overrideSDK stdenv "11.0" else stdenv;
        in {
          checks = import ./nix/test.nix {
            inherit (pkgs) system stdenv runCommand lib;
            inherit nixpkgs flake-utils;
            idris = self;
          };
          packages = rec {
            inherit (pkgs.idris2Packages) support idris2;
            idris2Api = pkgs.idris2Packages.idris2Api.library { withSource = true; };
            default = idris2;
          } // (import ./nix/text-editor.nix {
            inherit (pkgs) idris2;
            inherit pkgs idris-emacs-src;
          });
          inherit (pkgs.idris2Packages) buildIdris;
          devShells.default = pkgs.mkShell.override { stdenv = stdenv'; } {
            packages = pkgs.idris2.buildInputs;
          };
        };
    in lib.mkOvrOptsFlake
    (opts: flake-utils.lib.eachDefaultSystem (per-system opts) // sys-agnostic);
}
