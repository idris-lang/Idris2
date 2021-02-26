{
  description = "My Idris 2 package";

  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.idris = {
    url = github:guilhermehas/Idris2;
    inputs.flake-utils.follows = "flake-utils";
  };

  outputs = { self, idris, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
    let
      idrisPkgs = idris.packages.${system};
      pkg = idrisPkgs.buildIdris {
        projectName = "Foo";
        src = ./.;
      };
    in rec {
      packages = pkg // {
        inherit (idrisPkgs) idris;
      };
      defaultPackage = pkg;
    }
  );
}
