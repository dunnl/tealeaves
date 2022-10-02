{ pkgs ? import <nixpkgs> {} }:
let
  lib = pkgs.lib;
  mylib = import <nixpkgs/pkgs/build-support/coq/extra-lib.nix> {
    inherit lib;
  };
in with mylib; pkgs.coqPackages.mkCoqDerivation {
    pname = "tealeaves";
    owner = "dunnl";
    version = ./.;
    nativeBuildInputs = [
      pkgs.python310Packages.alectryon
      pkgs.coq
      pkgs.coqPackages.serapi
    ];
    propagatedBuildInputs =
      [ ];
    meta = {
      description = "A library for generic reasoning about syntax.";
      license = lib.licenses.mit;
    };
  }
