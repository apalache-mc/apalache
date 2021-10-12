{
  description = "A symbolic model checker for TLA+";

  inputs = {
    # Nix Inputs
    nixpkgs.url = github:nixos/nixpkgs/nixpkgs-unstable;
    pre-commit-hooks.url = github:cachix/pre-commit-hooks.nix;
    flake-utils.url = github:numtide/flake-utils;

  };

  outputs = { self, nixpkgs, pre-commit-hooks, flake-utils }:
    with flake-utils.lib;
    eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        # nix build
        packages = {
          dev-shell =
            pkgs.mkShell {
              shellHook = self.checks.${system}.pre-commit-check.shellHook;
              buildInputs = with pkgs; [
                jdk8
                scala_2_12
                metals
                maven
                scalafmt
                ocamlPackages.mdx
                python3
              ];
            };
        };

        # nix flake check
        checks = {
          pre-commit-check = pre-commit-hooks.lib.${system}.run {
            src = ./.;
            hooks = {
              nixpkgs-fmt.enable = true;
              nix-linter.enable = true;
              scalafmt = {
                enable = true;
                name = "scalafmt";
                entry = "${pkgs.scalafmt}/bin/scalafmt";
                files = "\\.scala$";
                language = "system";
                pass_filenames = false;
              };
            };
          };
        } // self.packages; # adding packages here ensures that every attr gets built on check

        # nix develop
        devShell = self.packages.${system}.dev-shell;
      });
}

