{ pkgs ? import <nixpkgs> {}
, inCI ? false
, coqDeps ? !inCI
}:

with pkgs;

let inherit (lib) optionals; in

let coqPackages = coqPackages_8_14; in

let coqword = callPackage ./coqword.nix { inherit coqPackages; }; in

let inherit (coqPackages.coq) ocamlPackages; in

if !lib.versionAtLeast ocamlPackages.ocaml.version "4.08"
then throw "Jasmin requires OCaml ≥ 4.08"
else

stdenv.mkDerivation {
  name = "jasmin-0";
  src = null;
  buildInputs = []
    ++ optionals coqDeps [ coqPackages.coq coqword coqPackages.coq.ocamlPackages.ocaml ]
    ;
}
