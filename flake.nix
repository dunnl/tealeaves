{
  description = "A flake for building Hello World";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixos-22.11;

  outputs = { self, nixpkgs }: {

    packages.x86_64-linux.default =
      let pkgs = nixpkgs { system = "x86_64-linux"; };
      in pkgs.coqPackages.mkCoqDerivation {
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
  }
}

