{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    opam-nix.url = "github:tweag/opam-nix";
    flake-utils.url = "github:numtide/flake-utils";
    ocamllsp.url = "git+https://www.github.com/ocaml/ocaml-lsp?submodules=1";
    ocamllsp.inputs.opam-nix.follows = "opam-nix";
    ocamllsp.inputs.nixpkgs.follows = "nixpkgs";
  };
  outputs = { self, flake-utils, opam-nix, nixpkgs, ocamllsp }@inputs:
    let package = "coq-lsp";
    in flake-utils.lib.eachDefaultSystem (system:
      let
        devPackages = {
          # Extra packages for testing
        };
      in
      {
        packages =
          let
            scope = opam-nix.lib.${system}.buildOpamProject' { } ./.
              (devPackages // { ocaml-base-compiler = "4.14.0"; });
          in
          scope // { default = self.packages.${system}.${package}; };

        devShell =
          let
            pkgs = nixpkgs.legacyPackages.${system};
          in
          pkgs.mkShell {
            nativeBuildInputs = [ pkgs.opam ];
            buildInputs = (with pkgs;
              [
                # dev tools
                ocamlformat_0_24_1
                nodejs
              ]) ++ [ ocamllsp.outputs.packages.${system}.ocaml-lsp-server ]
            ++ (builtins.map (s: builtins.getAttr s self.packages.${system})
              (builtins.attrNames devPackages));
            inputsFrom = [ self.packages.${system}.default ];
          };
      });
}
