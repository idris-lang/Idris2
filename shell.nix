{ pkgs ? import <nixpkgs> { } }:

pkgs.mkShell {
  nativeBuildInputs = with pkgs; [ chez clang gambit git nodejs racket idris2 ];
  buildInputs = with pkgs; [ gmp ];
}
