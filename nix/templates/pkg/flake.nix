{
  description = "My Idris 2 program";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.idris = {
    url = "github:idris-lang/Idris2";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.flake-utils.follows = "flake-utils";
  };

  outputs = { self, nixpkgs, idris, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        npkgs = import nixpkgs { inherit system; };
        idrisPkgs = idris.packages.${system};
        buildIdris = idris.buildIdris.${system};
        pkgs = buildIdris {
          projectName = "mypkg";
          src = ./.;
          idrisLibraries = [ ];
        };
      in rec {
        packages = pkgs // idrisPkgs;
        defaultPackage = pkgs.executable;
        devShell = npkgs.mkShell {
          buildInputs = [ idrisPkgs.idris2 npkgs.rlwrap ];
          shellHook = ''
            alias idris2="rlwrap -s 1000 idris2 --no-banner"
          '';
        };
      });
}
