{
  description = "Build scripts";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-22.11;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib; eachSystem allSystems (system:
    let
      pkgs = nixpkgs.legacyPackages.${system};
      lib = pkgs.lib;
      coq = pkgs.coq_8_16;
      ocamlPkgs = coq.ocamlPackages;
      coqPkgs = pkgs.coqPackages_8_16;
    in rec {
      packages = {
        coq-artifact = coqPkgs.mkCoqDerivation {
          pname = "coq-artifact";
          version = "main";
          src = ./.;
          buildPhase = "make";
          propagatedBuildInputs = [ ];
        };
      };
      devShell = import ./shell.nix { inherit pkgs; };
    });
}
