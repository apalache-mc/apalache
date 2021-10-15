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
    flake-utils.url = github:numtide/flake-utils;
  };

  # Outputs define the result of a flake. I use the term result to be intentionally vague since flakes
  # are overloaded. Flakes can be used as an interface for packaging software, describing NixOS system
  # configurations or modules, and even hydra jobs (hydra is nix's native CI solution). For our purposes
  # we only really care about the `devShell` output, since that is what provides the nix shell. For a
  # more thorough treatment of the nix flakes output schema see this resource:
  # https://zimbatm.com/NixFlakes/#output-schema
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib;
    eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
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

              # Commands that run when the shell starts
              shellHook = ''
                # Add common project environment variables
                source ./.envrc
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

                # Testing
                ocamlPackages.mdx
                python39Full
              ];
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

