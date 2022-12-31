{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    opam-nix.url = "github:tweag/opam-nix";
    flake-utils.url = "github:numtide/flake-utils";
    ocamllsp.url = "git+https://www.github.com/ocaml/ocaml-lsp?submodules=1";
    ocamllsp.inputs.opam-nix.follows = "opam-nix";
    ocamllsp.inputs.nixpkgs.follows = "nixpkgs";
    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
  };
  outputs = { self, flake-utils, opam-nix, nixpkgs, ocamllsp, opam-repository }@inputs:
    let package = "coq-lsp";
    in flake-utils.lib.eachDefaultSystem (system:
      let
        devPackages = {
          # Extra packages for testing
        };
        pkgs = nixpkgs.legacyPackages.${system};
        ocamlformat =
          # Detection of ocamlformat version from .ocamlformat file
          let
            ocamlformat_version =
              let
                lists = pkgs.lib.lists;
                strings = pkgs.lib.strings;
                ocamlformat_config = strings.splitString "\n" (builtins.readFile ./.ocamlformat);
                prefix = "version=";
                ocamlformat_version_pred = line: strings.hasPrefix prefix line;
                version_line = lists.findFirst ocamlformat_version_pred "not_found" ocamlformat_config;
                version = strings.removePrefix prefix version_line;
              in
              builtins.replaceStrings [ "." ] [ "_" ] version;
          in
          builtins.getAttr ("ocamlformat_" + ocamlformat_version) pkgs;
      in
      {
        packages =
          let
            scope = opam-nix.lib.${system}.buildOpamProject'
              {
                repos = [ opam-repository ];
              } ./.
              (devPackages // { ocaml-base-compiler = "4.14.0"; });
          in
          scope // { default = self.packages.${system}.${package}; };

        devShells.fmt =
          pkgs.mkShell {
            inputsFrom = [ pkgs.dune_3 ];
            buildInputs = [ pkgs.dune_3 ocamlformat ];
          };

        devShell =
          pkgs.mkShell {
            nativeBuildInputs = [ pkgs.opam ];
            buildInputs = (with pkgs;
              [
                # dev tools
                ocamlformat
                nodejs
              ]) ++ [ ocamllsp.outputs.packages.${system}.ocaml-lsp-server ]
            ++ (builtins.map (s: builtins.getAttr s self.packages.${system})
              (builtins.attrNames devPackages));
            inputsFrom = [ self.packages.${system}.default ];
          };
      });
}
