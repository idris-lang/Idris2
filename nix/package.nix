{ stdenv, lib, chez, clang, gmp, makeWrapper, installShellFiles, support, idris2Version
, srcRev, gambit, nodejs, zsh, idris2Bootstrap ? null }:

# Uses scheme to bootstrap the build of idris2
let
  bootstrap = idris2Bootstrap == null;
  supportLibrariesPath = lib.makeLibraryPath [ support ];
  supportSharePath = lib.makeSearchPath "share" [ support ];
in
stdenv.mkDerivation rec {
  pname = "idris2";
  version = idris2Version;

  # we don't rebuild Idris when changing the buildIdris nix
  # function:
  src = with lib.fileset; toSource {
    root = ../.;
    fileset = difference ../. ../nix/buildIdris.nix;
  };

  strictDeps = true;
  nativeBuildInputs = [ makeWrapper installShellFiles clang chez ]
    ++ lib.optional stdenv.isDarwin [ zsh ]
    ++ lib.optional (!bootstrap) [ idris2Bootstrap ];
  buildInputs = [ chez gmp support ];

  # For bootstrap builds the Makefile will try to
  # rebuild the support library if we don't patch
  # bootstrap-install.
  prePatch = ''
    patchShebangs --build tests
    substituteInPlace Makefile \
      --replace-fail '$(GIT_SHA1)' '${srcRev}'
  '' + lib.optionalString bootstrap ''
    substituteInPlace Makefile \
      --replace-fail 'bootstrap-install: install-idris2 install-support' 'bootstrap-install: install-idris2'
  '';

  makeFlags = [ "IDRIS2_SUPPORT_DIR=${supportLibrariesPath}" ]
    ++ lib.optional stdenv.isDarwin "OS=";

  # The name of the main executable of pkgs.chez is `scheme`
  buildFlags = [ "PREFIX=$(out)" ] ++
    lib.optional bootstrap [
      "bootstrap" "SCHEME=scheme"
      "IDRIS2_DATA=${supportSharePath}"
      "IDRIS2_LIBS=${supportLibrariesPath}"
    ];

  # checks happen against built compiler prior to the postInstall
  # wrapper below so we must augment some paths to point at prebuilt
  # support paths regardless of whether we are bootstrapping or not.
  checkInputs = [ gambit nodejs ]; # racket ];
  checkFlags = [
    "INTERACTIVE="
    "IDRIS2_DATA=${supportSharePath}"
    "IDRIS2_LIBS=${supportLibrariesPath}"
    "TEST_IDRIS2_DATA=${supportSharePath}"
    "TEST_IDRIS2_LIBS=${supportLibrariesPath}"
    "TEST_IDRIS2_SUPPORT_DIR=${supportLibrariesPath}"
  ];

  installTargets = "install-idris2 install-with-src-libs";
  installFlags = [ "PREFIX=$(out)" ];

  # TODO: Move this into its own derivation, such that this can be changed
  #       without having to recompile idris2 every time.
  postInstall = let
    name = "${pname}-${version}";
    globalLibraries = [
      "\\$HOME/.nix-profile/lib/${name}"
      "/run/current-system/sw/lib/${name}"
      "$out/${name}"
    ];
    globalLibrariesPath = builtins.concatStringsSep ":" globalLibraries;
  in ''
    # Remove existing idris2 wrapper that sets incorrect LD_LIBRARY_PATH
    rm $out/bin/idris2

    # The only thing we need from idris2_app is the actual binary
    mv $out/bin/idris2_app/idris2.so $out/bin/idris2
    rm $out/bin/idris2_app/*
    rmdir $out/bin/idris2_app

    # idris2 needs to find scheme at runtime to compile
    # idris2 installs packages with --install into the path given by
    #   IDRIS2_PREFIX. We set that to a default of ~/.idris2, to mirror the
    #   behaviour of the standard Makefile install.
    wrapProgram "$out/bin/idris2" \
      --set-default CHEZ "${chez}/bin/scheme" \
      --run 'export IDRIS2_PREFIX=''${IDRIS2_PREFIX-"$HOME/.idris2"}' \
      --suffix IDRIS2_LIBS ':' "${supportLibrariesPath}" \
      --suffix IDRIS2_DATA ':' "${supportSharePath}" \
      --suffix IDRIS2_PACKAGE_PATH ':' "${globalLibrariesPath}" \
      --suffix LD_LIBRARY_PATH ':' "${supportLibrariesPath}" \
      --suffix DYLD_LIBRARY_PATH ':' "${supportLibrariesPath}" \

    installShellCompletion --cmd idris2 \
      --bash <($out/bin/idris2 --bash-completion-script idris2) \
      --zsh <($out/bin/idris2 --zsh-completion-script idris2) \
  '';
}
