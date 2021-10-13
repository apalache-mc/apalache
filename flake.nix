{
  description = "A symbolic model checker for TLA+";

  inputs = {
    # Nix Inputs
    nixpkgs.url = github:nixos/nixpkgs/nixpkgs-unstable;
    nixpkgs-scalafmt-275.url = github:nixos/nixpkgs/14bcebe82882e4bc2c71c95da4fce1c9d1651575;
    pre-commit-hooks.url = github:JonathanLorimer/pre-commit-hooks.nix;
    flake-utils.url = github:numtide/flake-utils;

  };

  outputs = { self, nixpkgs, nixpkgs-scalafmt-275, pre-commit-hooks, flake-utils }:
    with flake-utils.lib;
    eachDefaultSystem (system:
      let
        pkgs-scalafmt-275 = import nixpkgs-scalafmt-275 { inherit system; };
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            (_: _: { scalafmt = pkgs-scalafmt-275.scalafmt; })
          ];
        };
      in
      {
        # nix build
        packages = {
          dev-shell =
            pkgs.mkShell {
              shellHook = self.checks.${system}.pre-commit-check.shellHook;
              buildInputs = with pkgs; [
                # Java / Scala
                jdk8
                scala_2_12

                # Build
                maven

                # Development
                metals
                scalafmt

                # Testing
                opam
                ocamlPackages.mdx
                python39Full
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
        };

        # nix develop
        devShell = self.packages.${system}.dev-shell;
      });
}

