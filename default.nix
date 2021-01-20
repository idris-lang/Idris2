{ nixpkgs ? import <nixos> {} }: with nixpkgs;

callPackage ./package.nix {}
