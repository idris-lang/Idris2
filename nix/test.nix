{ nixpkgs
, idris
, flake-utils
, system
, stdenv
, runCommand
, lib
}:
let
  withTests = tests: drv:
    let testDrvs = lib.mapAttrs
      (name: testScript:
        runCommand "${drv.name}-test-${name}"
          {} ''
            ${testScript}
            touch "$out"
          '') tests;
     in testDrvs;
  self = import ./templates/pkg/flake.nix;
  template = self.outputs { inherit self nixpkgs idris flake-utils; };
  templateBuild = template.packages.${system}.build;
  testsTemplate = {
    checkFoo = ''
      ${templateBuild}/bin/runMyPkg \
        | grep "Foo"
    '';
  };
in
withTests testsTemplate templateBuild
