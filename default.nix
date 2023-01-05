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
      description = "A Coq framework for reusable syntax metatheory.";
      longDescription = ''
        Tealeaves is a Coq framework for building reusable libraries
        of formal syntax metatheory called backends. Backends can be
        used by to develop languages formalized in Coq.
      '';
      homepage = https://tealeaves.science;
      license = lib.licenses.mit;
    };
}
