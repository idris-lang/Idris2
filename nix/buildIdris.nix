{ stdenv, lib, idris2Version, idris2, jq, support, makeWrapper }:
# Usage: let
#          pkg = idris2Pkg.buildIdris {
#            src = ...;
#            ipkgName = "my-pkg";
#            idrisLibraries = [ ];
#          };
#        in {
#          lib = pkg.library { withSource = true; };
#          bin = pkg.executable;
#        }
#
{ src
, ipkgName
, version ? "unversioned"
, idrisLibraries # Other libraries built with buildIdris
, ... }@attrs:

let
  # loop over idrisLibraries and normalize them by turning any that are
  # direct outputs of the buildIdris function into the `.library {}`
  # property.
  idrisLibraryLibs = map (idrisLib:
    if lib.isDerivation idrisLib
    then idrisLib
    else if builtins.isFunction idrisLib
    then idrisLib {}
    else if (builtins.isAttrs idrisLib && idrisLib ? "library")
    then idrisLib.library {}
    else throw "Found an Idris2 library dependency that was not the result of the buildIdris function"
  ) idrisLibraries;

  propagate = libs: lib.unique (lib.concatMap (nextLib: [nextLib] ++ nextLib.propagatedIdrisLibraries) libs);
  ipkgFileName = ipkgName + ".ipkg";
  idrName = "idris2-${idris2Version}";
  libSuffix = "lib/${idrName}";
  propagatedIdrisLibraries = propagate idrisLibraryLibs;
  libDirs =
    lib.strings.makeSearchPath libSuffix propagatedIdrisLibraries;
  drvAttrs = builtins.removeAttrs attrs [
    "ipkgName"
    "idrisLibraries"
  ];

  derivation = stdenv.mkDerivation (finalAttrs:
    drvAttrs // {
      pname = ipkgName;
      inherit version;
      src = src;
      nativeBuildInputs = [ idris2 makeWrapper jq ] ++ attrs.nativeBuildInputs or [];
      buildInputs = propagatedIdrisLibraries ++ attrs.buildInputs or [];

      IDRIS2_PACKAGE_PATH = libDirs;

      buildPhase = ''
        runHook preBuild
        idris2 --build ${ipkgFileName}
        runHook postBuild
      '';

      passthru = {
        inherit propagatedIdrisLibraries;
      };

      shellHook = ''
        export IDRIS2_PACKAGE_PATH="${finalAttrs.IDRIS2_PACKAGE_PATH}"
      '';
    }
  );

in rec {
  executable = derivation.overrideAttrs {
    installPhase = ''
      runHook preInstall
      mkdir -p $out/bin
      scheme_app="$(find ./build/exec -name '*_app')"
      if [ "$scheme_app" = ''' ]; then
        mv -- build/exec/* $out/bin/
        chmod +x $out/bin/*
        # ^ remove after Idris2 0.8.0 is released. will be superfluous:
        # https://github.com/idris-lang/Idris2/pull/3189
      else
        executable="$(idris2 --dump-ipkg-json ${ipkgFileName} | jq -r '.executable').so"

        cd build/exec/*_app

        rm -f ./libidris2_support.{so,dylib}

        bin_name="''${executable%.so}"
        mv -- "$executable" "$out/bin/$bin_name"

        # remaining .so or .dylib files can be moved to lib directory
        for file in *{.so,.dylib}; do
          mkdir -p $out/lib
          mv -- "$file" "$out/lib/"
        done

        wrapProgram "$out/bin/$bin_name" \
          --prefix LD_LIBRARY_PATH : ${lib.makeLibraryPath [ support ]}:$out/lib \
          --prefix DYLD_LIBRARY_PATH : ${lib.makeLibraryPath [ support ]}:$out/lib

      fi
      runHook postInstall
    '';
  };

  library = { withSource ? false }:
    let installCmd = if withSource then "--install-with-src" else "--install";
    in derivation.overrideAttrs {
      installPhase = ''
        runHook preInstall
        mkdir -p $out/${libSuffix}
        export IDRIS2_PREFIX=$out/lib
        idris2 ${installCmd} ${ipkgFileName}
        runHook postInstall
      '';
    };
  # deprecated aliases:
  build = lib.warn "build is a deprecated alias for 'executable'." executable;
  installLibrary = lib.warn "installLibrary is a deprecated alias for 'library { }'." (library { });
}
