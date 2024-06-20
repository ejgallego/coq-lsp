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

          propagatedBuildInputs = l.attrValues {
            inherit
              (ocamlPackages)
              cmdliner
              findlib
              ppx_deriving
              ppx_deriving_yojson
              ppx_import
              ppx_sexp_conv
              ppx_hash
              sexplib
              yojson
              zarith
              uri
              dune-build-info
              ppx_inline_test
              logs
              lwt
              ;
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
            inherit (ocamlPackages) ocaml ocamlformat ocaml-lsp;
          };
        };
      };
    };
}
