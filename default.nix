{
  pkgs ? import (fetchTarball "https://github.com/vbgl/nixpkgs/tarball/2a4e60c330d66638897ec450126eb1e3a9a13148") {}
}:

with pkgs;

let oc = ocaml-ng.ocamlPackages_4_07; in

stdenv.mkDerivation {
  name = "coq-lsp-0";
  buildInputs = [
    dune oc.ocaml oc.findlib oc.num oc.yojson oc.cmdliner
    oc.lablgtk
  ];
}
