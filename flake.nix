{
  description = "A flake for building Tealeaves";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixos-22.11;

  outputs = { self, nixpkgs }:
    let pkgs = import nixpkgs {
          system = "x86_64-linux";
        };
        tealeaves = pkgs.callPackage ./tealeaves.nix {
          version = "dunnl:master";
        };
    in { packages.x86_64-linux.default = tealeaves;
         packages.x86_64-linux.tealeaves = tealeaves;
         devShells.x86_64-linux.default = tealeaves;
         devShells.x86_64-linux.tealeaves = tealeaves;
       };
}
