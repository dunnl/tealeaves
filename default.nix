{ pkgs ? import <nixpkgs> {} }:
let
  lib = pkgs.lib;
  coq-tealeaves-stlc =
    pkgs.stdenv.mkDerivation {
      pname = "tealeaves-stlc";
      owner = "dunnl";
      version = ./.;
      src = pkgs.nix-gitignore.gitignoreSource [] ./.;
      nativeBuildInputs = [
        pkgs.coq
        pkgs.coqPackages.serapi
        pkgs.python310Packages.alectryon
        coq-tealeaves
      ];
      propagatedBuildInputs =
        [ ];
      buildPhase = ''
        mkdir tmp; mkdir tmp/STLC; mkdir tmp/SystemF
        alectryon Tealeaves/Examples/STLC/Language.v --output-directory tmp/STLC
        alectryon Tealeaves/Examples/STLC/Theory.v --output-directory tmp/STLC
        alectryon Tealeaves/Examples/SystemF/Language.v --output-directory tmp/SystemF
        alectryon Tealeaves/Examples/SystemF/Theory.v --output-directory tmp/SystemF
      '';
      phases = [ "unpackPhase" "buildPhase" "installPhase" ];
      installPhase = ''
        mkdir -p $out;
        mv tmp/STLC $out;
        mv tmp/SystemF $out;
      '';
      meta = {
        description = "Alectryon-generated file for Tealeaves STLC demo.";
        longDescription = ''
        Alectryon-generated file for Tealeaves STLC demo.
      '';
        homepage = https://tealeaves.science;
        license = lib.licenses.mit;
      };
    };
  coq-tealeaves =
    pkgs.coqPackages.mkCoqDerivation {
      pname = "tealeaves";
      owner = "dunnl";
      version = ./.;
      src = pkgs.nix-gitignore.gitignoreSource ["*.nix"] ./.;
      nativeBuildInputs = [
        pkgs.coq
        pkgs.ocaml # `ocaml` is needed for `ocamldoc`, which is needed to make Makefile.coq happy
      ];
      propagatedBuildInputs =
        [ ];
      installTargets = "install install-doc";
      extraInstallFlags = ["DOCDIR=$(out)/share/coq/${pkgs.coq.coq-version}/"];
      meta = {
        description = "A Coq framework for reusable syntax metatheory.";
        longDescription = ''
        Tealeaves is a Coq framework for building reusable metatheory
        for extrinsically typed first-order abstract syntax.
      '';
        homepage = https://tealeaves.science;
        license = lib.licenses.mit;
      };
    };
in
{ inherit coq-tealeaves coq-tealeaves-stlc;
}
