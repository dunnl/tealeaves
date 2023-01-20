{ pkgs ? import <nixpkgs> {}
, tealeaves ? import ../../../. {}
, no-tealeaves ? false}:
pkgs.stdenv.mkDerivation {
  name = "tealeaves-stlc";
  src = ./.;
  nativeBuildInputs = with pkgs; [
    coq
    ocamlPackages.findlib
    python310Packages.alectryon
    coqPackages.serapi
  ] ++ (if no-tealeaves
         then []
         else [tealeaves]);

}
