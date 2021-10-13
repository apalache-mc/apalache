# Reference material for nix flakes:
#   1. nix wiki: https://nixos.wiki/wiki/Flakes
#   2. serokell blog (casual introduction): https://serokell.io/blog/practical-nix-flakes
#   3. tweag blog (explanation of motivation, expects some knowledge of nix):
#   https://www.tweag.io/blog/2020-05-25-flakes/

{
  description = "A symbolic model checker for TLA+";

  # Inputs follow their own schema https://zimbatm.com/NixFlakes/#input-schema, but for the
  # user who just wants a high level understanding, these can be thought of as our explicit
  # dependencies.
  inputs = {
    # Nix Inputs
    nixpkgs.url = github:nixos/nixpkgs/nixpkgs-unstable;
    nixpkgs-scalafmt-275.url = github:nixos/nixpkgs/14bcebe82882e4bc2c71c95da4fce1c9d1651575;
    pre-commit-hooks.url = github:JonathanLorimer/pre-commit-hooks.nix;
    flake-utils.url = github:numtide/flake-utils;

  };

  # Outputs define the result of a flake. I use the term result to be intentionally vague since flakes
  # are overloaded. Flakes can be used as an interface for packaging software, describing NixOS system
  # configurations or modules, and even hydra jobs (hydra is nix's native CI solution). For our purposes
  # we only really care about the `devShell` output, since that is what provides the nix shell. For a
  # more thorough treatment of the nix flakes output schema see this resource:
  # https://zimbatm.com/NixFlakes/#output-schema
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

        # Nix Build
        # Command: `nix build .#<attr-name>`
        # Reference documentation: https://nixos.org/manual/nix/unstable/command-ref/new-cli/nix3-build.html
        # Nix build is traditionally used to provide derivations for distribution, you can think of a
        # derivation as a very thorough description of everything that is required for nix to build your
        # software. We are using this exclusively to package up our nix shell environments, while building
        # these won't yield a result, nix can provide access to the environment described in the derivation.
        # The reason we use packages, instead of the devShell attribute directly, is so that we can potentially
        # provide multiple shells in the future.
        packages = {
          dev-shell =
            pkgs.mkShell {
              # shellHook is invoked immediately upon entering the nix shell. Right now we do 2 things here:
              #   1. write the pre-commit hook, so that git can pick it up.
              #   2. check that opam has been initialized for integration tests.
              shellHook = ''
                ${self.checks.${system}.pre-commit-check.shellHook}
                if ${pkgs.opam}/bin/opam env >/dev/null 2>&1; then
                  :
                else
                  echo "⚠️ need to initialize opam ⚠️"
                  ${pkgs.opam}/bin/opam init
                fi

              '';

              # Built inputs are the packages that we provide in the PATH in the nix shell
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

        # Nix Check
        # Command: `nix flake check`
        # Reference documentation: https://nixos.org/manual/nix/unstable/command-ref/new-cli/nix3-flake-check.html
        # This is the command that is generally used to test your software. In our case the only check we are
        # providing is the pre commit hook. This allows you to run the pre commit hook manually, which can be
        # nice for debugging or a faster feedback cycle.
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

        # Nix Develop
        # Command: `nix develop`
        # Reference documentation: https://nixos.org/manual/nix/unstable/command-ref/new-cli/nix3-develop.html
        # This is the attribute that provides the default shell; the shell that is provided when nix develop is
        # invoked. You can run a non-default shell, that is provided in the packages attr, by running
        # `nix develop .#<attr-name>`. You can test running a non-default shell by invoking `nix develop .#dev-shell`.
        # NOTE: dev-shell is the same as the default shell, since we only provide 1 shell at this time.
        devShell = self.packages.${system}.dev-shell;
      });
}

