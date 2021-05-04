{ stdenv
, lib
, chez
, clang
, fetchFromGitHub
, makeWrapper
, idris2-version
, racket
, gambit
, nodejs
}:

# Uses scheme to bootstrap the build of idris2
stdenv.mkDerivation rec {
  pname = "idris2";
  version = idris2-version;

  src = ../.;

  strictDeps = true;
  nativeBuildInputs = [ makeWrapper clang chez ];
  buildInputs = [ chez ];

  prePatch = ''
    patchShebangs --build tests
  '';

  makeFlags = [ "PREFIX=$(out)" ]
    ++ lib.optional stdenv.isDarwin "OS=";

  # The name of the main executable of pkgs.chez is `scheme`
  buildFlags = [ "bootstrap" "SCHEME=scheme" ];

  checkInputs = [ gambit nodejs ]; # racket ];
  checkFlags = [ "INTERACTIVE=" ];

  # TODO: Move this into its own derivation, such that this can be changed
  #       without having to recompile idris2 every time.
  postInstall = let
    includedLibs = [ "base" "contrib" "network" "prelude" "test" ];
    name = "${pname}-${version}";
    packagePaths = builtins.map (l: "$out/${name}/${l}-${version}") includedLibs;
    additionalIdris2Paths = builtins.concatStringsSep ":" packagePaths;
    globalLibraries = [ "\\$HOME/.nix-profile/lib/${name}" "/run/current-system/sw/lib/${name}" ];
    globalLibrariesPath = builtins.concatStringsSep ":" globalLibraries;
  in ''
    # Remove existing idris2 wrapper that sets incorrect LD_LIBRARY_PATH
    rm $out/bin/idris2
    # Move actual idris2 binary
    mv $out/bin/idris2_app/idris2.so $out/bin/idris2
    # After moving the binary, there is nothing left in idris2_app that isn't
    # either contained in lib/ or is useless to us.
    rm $out/bin/idris2_app/*
    rmdir $out/bin/idris2_app
    # idris2 needs to find scheme at runtime to compile
    # idris2 installs packages with --install into the path given by PREFIX.
    # Since PREFIX is in nix-store, it is immutable so --install does not work.
    # If the user redefines PREFIX to be able to install packages, idris2 will
    # not find the libraries and packages since all paths are relative to
    # PREFIX by default.
    # We explicitly make all paths to point to nix-store, such that they are
    # independent of what IDRIS2_PREFIX is. This allows the user to redefine
    # IDRIS2_PREFIX and use --install as expected.
    # TODO: Make support libraries their own derivation such that
    #       overriding LD_LIBRARY_PATH is unnecessary
    # TODO: Maybe set IDRIS2_PREFIX to the users home directory
    wrapProgram "$out/bin/idris2" \
      --set-default CHEZ "${chez}/bin/scheme" \
      --suffix IDRIS2_LIBS ':' "$out/${name}/lib" \
      --suffix IDRIS2_DATA ':' "$out/${name}/support" \
      --suffix IDRIS2_PATH ':' "${additionalIdris2Paths}" \
      --run "export IDRIS2_PACKAGE_PATH=\$IDRIS2_PACKAGE_PATH:${globalLibrariesPath}" \
      --suffix LD_LIBRARY_PATH ':' "$out/${name}/lib"
  '';
}
