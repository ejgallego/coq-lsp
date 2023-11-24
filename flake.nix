{
  description = "A language server (LSP) for the Coq theorem prover";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    treefmt.url = "github:numtide/treefmt-nix";

    napalm.url = "github:nix-community/napalm";

    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };

    coq-serapi = {
      url = "github:ejgallego/coq-serapi/v8.18";
      flake = false;
    };
  };

  outputs = inputs @ {
    self,
    flake-parts,
    treefmt,
    ...
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      systems = ["x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin"];
      imports = [treefmt.flakeModule ./editor/code/flakeModule.nix];

      perSystem = {
        config,
        pkgs,
        lib,
        ...
      }: let
        l = lib // builtins;
        coqpkg = pkgs.coqPackages_8_18;
        coqPackages = coqpkg.coqPackages;
        ocamlPackages = coqpkg.coq.ocamlPackages;
      in {
        packages.default = config.packages.coq-lsp;

        # NOTE(2023-06-02): Nix does not support top-level self submodules (yet)
        packages.coq-lsp = ocamlPackages.buildDunePackage {
          duneVersion = "3";

          pname = "coq-lsp";
          version = "${self.lastModifiedDate}+8.18-rc1";

          src = self.outPath;

          nativeBuildInputs = l.attrValues {
            inherit (ocamlPackages) menhir;
          };

          propagatedBuildInputs = let
            serapi =
              (coqPackages.lib.overrideCoqDerivation {
                  defaultVersion = "8.18.0+0.18.0";
                }
                coqPackages.serapi)
              .overrideAttrs (_: {
                src = inputs.coq-serapi;
              });
          in
            l.attrValues {
              inherit serapi;
              inherit (ocamlPackages) yojson cmdliner uri dune-build-info;
            };
        };

        treefmt.config = {
          projectRootFile = "dune-project";

          flakeFormatter = true;

          settings.global.excludes = ["./vendor/**"];

          programs.alejandra.enable = true;
          programs.ocamlformat = {
            enable = true;
            configFile = ./.ocamlformat;
          };
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = [config.packages.coq-lsp];

          packages = l.attrValues {
            inherit (config.treefmt.build) wrapper;
            inherit (pkgs) dune_3 nodejs dune-release;
            inherit (ocamlPackages) ocaml ocaml-lsp alcotest;
          };
        };
      };
    };
}
