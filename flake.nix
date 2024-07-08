{
  description = "A formal verification of the polkadot Grandpa protocol";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        makeDevShell = { coq ? pkgs.coq }:
          let
            coqPackages = pkgs.mkCoqPackages coq // {
              __attrsFailEvaluation = true;
            };
          in { extraPackages ? [ coqPackages.coq-lsp ] }:
          pkgs.mkShell {
            buildInputs = with coqPackages;
              [ pkgs.dune_3 pkgs.ocaml ] ++ extraPackages ++ [ coq ];
          };
      in {
        packages.default = pkgs.coqPackages.mkCoqDerivation {
          pname = "grandpa";
          version = "8.19";
          src = self;
          useDune = true;
        };

        devShells.default = makeDevShell { coq = pkgs.coq_8_19; } { };

        # To use, pass --impure to nix develop
        devShells.coq_master =
          makeDevShell { coq = pkgs.coq.override { version = "master"; }; } { };

        formatter = pkgs.nixpkgs-fmt;
      });
}
