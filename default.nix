{ pkgs ? import <nixpkgs> {} }:
let
  lib = pkgs.lib;
  coq-tealeaves =
    pkgs.coqPackages.mkCoqDerivation {
      pname = "tealeaves";
      owner = "dunnl";
      version = ./.;
      src = pkgs.nix-gitignore.gitignoreSource [] ./.;
      nativeBuildInputs = [
        pkgs.coq
      ];
      propagatedBuildInputs =
        [ ];
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
  coq-tealeaves-doc =
    pkgs.coqPackages.mkCoqDerivation {
      pname = "tealeaves";
      owner = "dunnl";
      version = ./.;
      src = pkgs.nix-gitignore.gitignoreSource [] ./.;
      nativeBuildInputs = [
        pkgs.coq
        pkgs.ocaml # Needed for `ocamldoc`, which is need to make Makefile.coq happy
        #pkgs.coqPackages.serapi
        #pkgs.python310Packages.alectryon
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
{ inherit coq-tealeaves-doc;
}
