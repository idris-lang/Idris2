{ pkgs ? import <nixos> {} }: with pkgs;

callPackage ./nix/package.nix {}
