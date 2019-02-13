{
  pkgs ? import (fetchTarball "https://github.com/vbgl/nixpkgs/tarball/2a4e60c330d66638897ec450126eb1e3a9a13148") {}
}:

with pkgs;

let oc = ocaml-ng.ocamlPackages_4_07; in

stdenv.mkDerivation {
  name = "coq-lsp-0";
  src = builtins.filterSource (p: _: builtins.baseNameOf p != "_build") ./.;
  buildInputs = [
    dune oc.ocaml oc.findlib oc.num oc.yojson oc.cmdliner
    oc.lablgtk
  ];

  preBuild = ''
    for f in kernel dev/tools
    do
      patchShebangs coq/$f
    done
  '';

  inherit (dune) installPhase;
}
