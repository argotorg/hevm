{
  description = "hevm";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    foundry = {
      url = "github:shazow/foundry.nix/stable";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
    solidity = {
      url = "github:argotorg/solidity/fd3a22656ebe9c91a96ebd846ab7699b5f2e053c";
      flake = false;
    };
    forge-std = {
      url = "github:foundry-rs/forge-std";
      flake = false;
    };
    empty-smt-solver = {
      url = "github:msooseth/empty-smt-solver/74bd120fdb730fde8e44243305e669e5e8a3e02a";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
    solc-pkgs = {
      url = "github:hellwolf/solc.nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
  };

  outputs = { nixpkgs, flake-utils, solidity, empty-smt-solver, forge-std, foundry, solc-pkgs, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = (import nixpkgs {
          inherit system;
          overlays = [
            foundry.overlay
            solc-pkgs.overlay
          ];
        });
        execution-spec-tests-fixtures = pkgs.stdenv.mkDerivation {
          name = "execution-spec-tests-fixtures";
          src = pkgs.fetchurl {
            url = "https://github.com/ethereum/execution-spec-tests/releases/download/v5.4.0/fixtures_develop.tar.gz";
            hash = "sha256-PisC1J/pA+2k/Yyspcvw0TnEcOl+HemoUpmxsDT5cJk=";
          };
          phases = [ "unpackPhase" ];
          unpackPhase = ''
            mkdir -p $out
            tar xf $src --strip-components=1 -C $out "fixtures/blockchain_tests"
            # remove pure non-Osaka fixtures
            grep -rLZ '"network": "Osaka"' $out | xargs -0 rm
          '';
        };
        solc = (solc-pkgs.mkDefault pkgs pkgs.solc_0_8_31);
        foundry-bin = pkgs.foundry-bin.overrideAttrs (old: {
          # Foundry's ARM64 Linux binaries depend on libudev.
          buildInputs = (old.buildInputs or [])
            ++ pkgs.lib.optionals pkgs.stdenv.hostPlatform.isLinux [ pkgs.udev ];
        });
        testDeps = [
          solc
          foundry-bin
          pkgs.go-ethereum
          pkgs.z3
          pkgs.cvc5
          pkgs.git
          pkgs.bitwuzla
        ];

        hspkgs = ps: ps.haskell.packages.ghc912;
        hlib = pkgs.haskell.lib;

        # base hevm derivation.
        # parameterized on the pkgs definition to allow use of `pkgsStatic` or `pkgs` as needed.
        hevmBase = ps :
          ps.lib.pipe
            (((hspkgs ps).callCabal2nix "hevm" ./. {}).overrideAttrs(final: prev: {
              HEVM_SOLIDITY_REPO = solidity;
              HEVM_ETHEREUM_TESTS_REPO = "${execution-spec-tests-fixtures}/blockchain_tests";
              HEVM_FORGE_STD_REPO = forge-std;
              DAPP_SOLC = "${solc}/bin/solc";
            }))
            [
              (hlib.compose.overrideCabal (old: { testTargets = ["test"]; }))
              (hlib.compose.addTestToolDepends testDeps)
              (hlib.compose.appendConfigureFlags [ "-fci" "-O2" ])
              hlib.compose.dontHaddock
              hlib.compose.doCheck
            ];

        # "static" binary for distribution
        # on linux this is actually a real fully static binary
        # on macos only system libraries and frameworks remain dynamically
        # linked, so the binary does not require a Nix installation.
        hevmRedistributable = let
          grep = "${pkgs.gnugrep}/bin/grep";
          otool = "${pkgs.darwin.binutils.bintools}/bin/otool";
          install_name_tool = "${pkgs.darwin.binutils.bintools}/bin/install_name_tool";
          codesign_allocate = "${pkgs.darwin.binutils.bintools}/bin/codesign_allocate";
          codesign = "${pkgs.darwin.sigtool}/bin/codesign";
        in if pkgs.stdenv.hostPlatform.isLinux
        # The release executable does not use profiling libraries. Building
        # hevm's profiling library can crash the musl external interpreter.
        then hlib.disableLibraryProfiling (hlib.dontCheck (hevmBase pkgs.pkgsStatic))
        else pkgs.runCommand "stripNixRefs" {} ''
          mkdir -p $out/bin
          cp ${hlib.dontCheck (forceStaticDepsMacos (hevmBase pkgs))}/bin/hevm $out/bin/

          # get the list of dynamic libs from otool and tidy the output
          libs=$(${otool} -L $out/bin/hevm | tail -n +2 | sed 's/^[[:space:]]*//' | cut -d' ' -f1)

          # Some toolchains already link against the system C++ libraries.
          # Rewrite only the libraries that still point into the Nix store.
          chmod 777 $out/bin/hevm
          for lib in $libs; do
            case "$lib" in
              /nix/store/*/libc++.*) target=/usr/lib/libc++.1.dylib ;;
              /nix/store/*/libc++abi.*) target=/usr/lib/libc++abi.dylib ;;
              /nix/store/*/libiconv.*) target=/usr/lib/libiconv.dylib ;;
              *) continue ;;
            esac
            ${install_name_tool} -change "$lib" "$target" $out/bin/hevm
          done
          # check that no nix deps remain
          nixdeps=$(${otool} -L $out/bin/hevm | tail -n +2 | { ${grep} /nix/store -c || test $? = 1; })
          if [ ! "$nixdeps" = "0" ]; then
            echo "Nix deps remain in redistributable binary!"
            exit 255
          fi
          # re-sign binary
          CODESIGN_ALLOCATE=${codesign_allocate} ${codesign} -f -s - $out/bin/hevm
          chmod 555 $out/bin/hevm
        '';


        # wrapped binary for use on systems with nix available.
        # does not statically link.
        # ensures all required runtime deps are available and on path.
        hevmWrapped =
          pkgs.symlinkJoin {
            name = "hevm";
            paths = [ (hlib.dontCheck (hevmBase pkgs)) ];
            buildInputs = [ pkgs.makeWrapper ];
            postBuild = ''
              wrapProgram $out/bin/hevm \
                --prefix PATH : "${pkgs.lib.makeBinPath [
                  pkgs.bash
                  pkgs.coreutils
                  pkgs.git
                  pkgs.z3
                  pkgs.cvc5
                  pkgs.bitwuzla
                  solc
                ]}"
            '';
          };

        # if we pass a library folder to ghc via --extra-lib-dirs that contains
        # only .a files, then ghc will link that library statically instead of
        # dynamically (even if --enable-executable-static is not passed to cabal).
        # we use this trick to force static linking of some libraries on macos.
        stripDylib = drv : pkgs.runCommand "${drv.name}-strip-dylibs" {} ''
          mkdir -p $out
          mkdir -p $out/lib
          cp -r ${drv}/* $out/
          rm -rf $out/**/*.dylib
        '';

        # ensures that all required deps will be linked statically on macos builds
        forceStaticDepsMacos = p :
          hlib.appendConfigureFlags p
            [
              "--extra-lib-dirs=${stripDylib (pkgs.gmp.override { withStatic = true; })}/lib"
              "--extra-lib-dirs=${stripDylib (pkgs.libff.override { enableStatic = true; })}/lib"
              "--extra-lib-dirs=${pkgs.zlib.static}/lib"
              "--extra-lib-dirs=${stripDylib (pkgs.libffi.overrideAttrs (_: { dontDisableStatic = true; }))}/lib"
              "--extra-lib-dirs=${stripDylib (pkgs.ncurses.override { enableStatic = true; })}/lib"
            ];


      in rec {

        # --- packages ----

        packages.ci = pkgs.lib.pipe (hevmBase pkgs) (with hlib.compose; [doBenchmark dontHaddock disableLibraryProfiling]);
        packages.unwrapped = hlib.dontCheck (hevmBase pkgs);
        packages.hevm = hevmWrapped;
        packages.redistributable = hevmRedistributable;
        packages.default = packages.hevm;

        # --- apps ----

        apps.hevm = flake-utils.lib.mkApp { drv = packages.hevm; };
        apps.default = apps.hevm;

        # --- shell ---

        devShells.default = let
          libraryPath = "${pkgs.lib.makeLibraryPath [ pkgs.libff pkgs.gmp ]}";
        in (hspkgs pkgs).shellFor {
          packages = _: [ (hevmBase pkgs) ];
          doBenchmark = true;
          buildInputs = [
            pkgs.curl
            pkgs.mdbook
            pkgs.mdbook-mermaid
            pkgs.yarn
            (hspkgs pkgs).cabal-install
            (hspkgs pkgs).eventlog2html
            (hspkgs pkgs).haskell-language-server
            empty-smt-solver.packages.${system}.default
          ] ++ testDeps;
          withHoogle = true;

          # hevm tests expect these to be set
          HEVM_SOLIDITY_REPO = solidity;
          DAPP_SOLC = "${solc}/bin/solc";
          HEVM_ETHEREUM_TESTS_REPO = "${execution-spec-tests-fixtures}/blockchain_tests";
          HEVM_FORGE_STD_REPO = forge-std;

          # point cabal repl to system deps
          LD_LIBRARY_PATH = libraryPath;
          shellHook = pkgs.lib.optionalString pkgs.stdenv.hostPlatform.isDarwin ''
            export DYLD_LIBRARY_PATH="${libraryPath}";
          '';
        };
      }
    );
}
