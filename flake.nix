{
  description = "A language server (LSP) for the coq theorem prover";

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
        coq_8_17 = pkgs.coqPackages_8_17;
        coqPackages = coq_8_17.coqPackages;
        ocamlPackages = coq_8_17.coq.ocamlPackages;
      in {
        packages.default = config.packages.coq-lsp;

        # NOTE(2023-06-02): Nix does not support top-level self submodules (yet)
        packages.coq-lsp = ocamlPackages.buildDunePackage {
          duneVersion = "3";

          pname = "coq-lsp";
          version = "${self.lastModifiedDate}+8.17-rc1";

          src = self.outPath;

          nativeBuildInputs = l.attrValues {
            inherit (ocamlPackages) menhir;
          };

          propagatedBuildInputs = let
            serapi =
              (coqPackages.lib.overrideCoqDerivation {
                  defaultVersion = "8.17.0+0.17.0";
                }
                coqPackages.serapi)
              .overrideAttrs (_: {
                src = inputs.coq-serapi;
              });
          in
            l.attrValues {
              inherit serapi;
              inherit (ocamlPackages) yojson cmdliner uri;
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
            inherit (pkgs) dune_3;
            inherit (ocamlPackages) ocaml ocaml-lsp;
          };
        };
      };
    };

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    treefmt.url = "github:numtide/treefmt-nix";

    napalm.url = "github:nix-community/napalm";

    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };

    coq-serapi = {
      url = "github:ejgallego/coq-serapi/v8.17";
      flake = false;
    };
  };
}
