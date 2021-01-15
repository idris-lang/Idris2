{
  description = "Idris2 flake";

  outputs = { self, nixpkgs }: {

    packages.x86_64-linux.idris2 = import ./default.nix { nixpkgs = nixpkgs.legacyPackages.x86_64-linux; };

    defaultPackage.x86_64-linux = self.packages.x86_64-linux.idris2;

  };
}
