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
        version = idris2Version;
        overlays.default = final: prev:
          let
            outputPackages = prev.lib.filterAttrs
              (n: _: n != "default" && n != "idris2Api")
              self.packages.${prev.system};
            idris2Api = final.callPackage ./nix/idris2Api.nix {
              inherit (final.idris2Packages) buildIdris;
              inherit idris2Version;
            };
          in
           {
             idris2Packages = prev.idris2Packages // outputPackages // { inherit idris2Api; };
             idris2 = final.idris2Packages.idris2;
           };
      };
      per-system = { config ? { }, overlays ? [ ] }:
        system:
        let
          pkgs = import nixpkgs { inherit config system overlays; };
          chezSupportsSystem = (system == "x86_64-linux")
            || (pkgs.lib.versionAtLeast pkgs.chez.version "10.0.0");
          chez = if chezSupportsSystem then
            pkgs.chez
          else
            pkgs.chez-racket;
          idris2Support = pkgs.callPackage ./nix/support.nix { inherit idris2Version; };
          idris2Bootstrap = pkgs.callPackage ./nix/package.nix {
            inherit idris2Version chez;
            idris2Bootstrap = null;
            support = idris2Support;
            srcRev = self.shortRev or "dirty";
          };
          idris2Pkg = pkgs.callPackage ./nix/package.nix {
            inherit idris2Version chez idris2Bootstrap;
            support = idris2Support;
            srcRev = self.shortRev or "dirty";
          };
          buildIdris = pkgs.callPackage ./nix/buildIdris.nix {
            inherit idris2Version;
            idris2 = idris2Pkg;
            support = idris2Support;
          };
          idris2ApiPkg = pkgs.callPackage ./nix/idris2Api.nix {
            inherit idris2Version buildIdris;
          };
        in {
          checks = import ./nix/test.nix {
            inherit (pkgs) system stdenv runCommand lib;
            inherit nixpkgs flake-utils;
            idris = self;
          };
          packages = rec {
            support = idris2Support;
            idris2 = idris2Pkg;
            idris2Api = idris2ApiPkg.library { withSource = true; };
            default = idris2;
          } // (import ./nix/text-editor.nix {
            inherit pkgs idris-emacs-src idris2Pkg;
          });
          inherit buildIdris;
          devShells.default = pkgs.mkShell{
            packages = idris2Pkg.buildInputs;
          };
        };
    in lib.mkOvrOptsFlake
    (opts: flake-utils.lib.eachDefaultSystem (per-system opts) // sys-agnostic);
}
