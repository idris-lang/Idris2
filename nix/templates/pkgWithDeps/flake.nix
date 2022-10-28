{
  description = "My Idris 2 package";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.idris = {
    url = "github:idris-lang/Idris2";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.flake-utils.follows = "flake-utils";
  };
  inputs.pkg = {
    url = "github:idris-lang/pkg";
    inputs.flake-utils.follows = "flake-utils";
    inputs.idris.follows = "idris";
  };

  outputs = { self, nixpkgs, idris, flake-utils, pkg }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        npkgs = import nixpkgs { inherit system; };
        my-pkg = pkg.packages.${system}.installLibrary;
        idrisPkgs = idris.packages.${system};
        buildIdris = idris.buildIdris.${system};
        pkgs = buildIdris {
          projectName = "pkgWithDeps";
          src = ./.;
          idrisLibraries = [ pkg ];
        };
      in rec {
        packages = pkgs // idrisPkgs;
        defaultPackage = pkgs.build;
        devShell = npkgs.mkShell {
          buildInputs = [ idrisPkgs.idris2 npkgs.rlwrap ];
          shellHook = ''
            alias idris2="rlwrap -s 1000 idris2 --no-banner"
          '';
        };
      });
}
