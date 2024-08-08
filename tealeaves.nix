{ lib, nix-gitignore, coq, coqPackages, ocaml, ocamlPackages, python310Packages, version ? null }:

coqPackages.mkCoqDerivation {
  pname = "tealeaves";
  owner = "dunnl";
  inherit version;
  src = nix-gitignore.gitignoreSourcePure
    [ "**"
      "!Tealeaves/"
      "!_CoqProject"
      "!Makefile"
      "!Makefile.coq.conf"
      "!Makefile.coq.local"
      "!extra/"
      #"*.vo*"
      "*.aux"
      "*.lia.cache"
      "*.glob"
    ] ./.;
  nativeBuildInputs = [
    ocaml # `ocaml` is needed for `ocamldoc`, which is needed to make Makefile.coq happy
    ocamlPackages.findlib
    coqPackages.autosubst
    python310Packages.alectryon
    coqPackages.serapi
  ];
  outputs = [ "out" "alectryon"];
  installTargets = "install install-doc install-alectryon";
  buildFlags = [ "-j1" ];
  #extraInstallFlags = ["DOCDIR=$(out)/share/coq/${coq.coq-version}/"];
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
