{ stdenv, nix-gitignore, coq, coq-autosubst, serapi, ocamlPackages, python310Packages, tealeaves ? null }:

stdenv.mkDerivation {
  name = "tealeaves-examples";
  src = nix-gitignore.gitignoreSource
    [ "docs/"
      "extra/*.sh"
      "images/"
      "LICENSE"
      "*.lock"
      "*.nix"
      "*.md"
    ] ./.;
  nativeBuildInputs = [
    coq
    coq-autosubst 
    ocamlPackages.findlib
    python310Packages.alectryon
    serapi
  ];
}
