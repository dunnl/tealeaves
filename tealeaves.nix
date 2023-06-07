{ lib, nix-gitignore, mkCoqDerivation, coq, ocaml, version ? null }:

mkCoqDerivation {
  pname = "tealeaves";
  owner = "dunnl";
  inherit version;
  src = nix-gitignore.gitignoreSource
    [ "docs/"
      "extra/*.sh"
      "images/"
      "LICENSE"
      "*.lock"
      "*.nix"
      "*.md"
      "Makefile.examples"
    ] ./.;
  nativeBuildInputs = [
    ocaml # `ocaml` is needed for `ocamldoc`, which is needed to make Makefile.coq happy
  ];
  installTargets = "install install-doc";
  buildFlags = [ "-j1" ];
  extraInstallFlags = ["DOCDIR=$(out)/share/coq/${coq.coq-version}/"];
  meta = {
    description = "A Coq framework for reusable syntax metatheory.";
    longDescription = ''
            Tealeaves is a Coq framework for building reusable metatheory
            for raw first-order abstract syntax.
          '';
    homepage = https://tealeaves.science;
    license = lib.licenses.mit;
  };
}
