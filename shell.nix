{ pkgs ? import <nixpkgs> {},
  tealeaves ? import ./. {}
}:
 tealeaves.coq-tealeaves
