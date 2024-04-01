{ stdenv, nix-gitignore, coq, serapi, ocamlPackages, python310Packages, tealeaves ? null }:

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
    ocamlPackages.findlib
    python310Packages.alectryon
    serapi
  ];
}
