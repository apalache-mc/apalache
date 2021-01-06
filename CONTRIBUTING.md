# Contributing

Thank you for your interest in contributing to Apalache!

Apalache is a symbolic model checker for [TLA+][].

<!-- TODO(shonfeder): Add code of conduct -->

The easiest
way to contribute is to [open a new issue][] to report a bug or a feature
request. If you want to contribute to the code base, [searching for "help
wanted"][help-wanted] is a good place to start. If you would like to begin
working on an existing issue, please indicate so by leaving a comment. If you'd
like to work on something else, open an issue to start the discussion.

The rest of this document outlines the best practices for contributing to
Apalache:

[TLA+]: https://lamport.azurewebsites.net/tla/tla.html
[help-wanted]: https://github.com/informalsystems/apalache/issues?q=is%3Aissue+is%3Aopen+label%3A%22help+wanted%22
[open a new issue]: https://github.com/informalsystems/apalache/issues/new/choose

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-refresh-toc -->
**Table of Contents**

- [Contributing](#contributing)
    - [Decision Making](#decision-making)
    - [Making a pull request](#making-a-pull-request)
    - [Dependencies](#dependencies)
        - [Environment](#environment)
    - [Development Environment](#development-environment)
        - [IntelliJ IDEA](#intellij-idea)
        - [Emacs](#emacs)
            - [Install `metals-emacs`](#install-metals-emacs)
                - [Arch](#arch)
            - [Doom Emacs](#doom-emacs)
            - [Vanilla Emacs](#vanilla-emacs)
    - [Testing](#testing)
        - [Unit tests](#unit-tests)
        - [Integration tests](#integration-tests)
            - [Installing Dependencies](#installing-dependencies)
            - [Running the tests](#running-the-tests)
        - [Continuous Integration](#continuous-integration)
    - [Changelog](#changelog)
    - [Releases](#releases)
        - [Prepare the release](#prepare-the-release)
        - [Cut the release](#cut-the-release)
        - [Advance the version on unstable](#advance-the-version-on-unstable)
        - [Announce the relesae](#announce-the-relesae)

<!-- markdown-toc end -->

## Decision Making

<!-- TODO(QUESTION): Do we want this much overhead to contributions? -->

When contributing to the project, the following process leads to the best chance
of landing changes:

1. All work on the code base should be motivated by a [Github Issue][]. The
   issue helps capture the problem we're trying to solve and allows for early
   feedback.
2. Once the issue is created, maintainers may request more detailed
   documentation in the form of a [Request for Comment (RFC)][rfc] or
   [Architectural Decision Record (ADR)][adr].
3. Discussion at the RFC stage will build collective understanding of the
   dimensions of the problem and help structure conversations around trade-offs.
4. When the problem is well understood but the solution leads to large
   structural changes to the code base, these changes should be proposed in the
   form of an ADR. The ADR will help build consensus on an overall strategy to
   ensure the code base maintains coherence in the larger context. If you are
   not comfortable with writing an ADR, you can open a less-formal issue and the
   maintainers will help you turn it into an ADR.
5. When the problem and proposed solution are well understood, implementation
   can begin by opening a [pull request](#making-a-pull-request).

## Making a pull request

We develop on the `unstable` branch and release stable code on `master`.

Nontrivial changes should start with a [draft pull request][] against
`unstable`. The draft signals that work is underway. When the work is ready for
feedback, hitting "Ready for Review" will signal to the maintainers that you are
ready for them to take a look.

Where possible, implementation trajectories should aim to proceed as a series of
small, logically distinct, incremental changes, in the form of small PRs that
can be merged quickly. This helps manage the load for reviewers and reduces the
likelihood that PRs will sit open for longer.

Each stage of the process is aimed at creating feedback cycles which align
contributors and maintainers to make sure:

- Contributors don’t waste their time implementing/proposing features which
  won’t land in `main`.
- Maintainers have the necessary context in order to support and review
  contributions.

## Dependencies

For setting up the local build, see the [instructions on building form
source](./docs/manual.md#building-from-source).

### Environment

The necessary shell environment is specified in [.envrc](./.envrc). You can:

- use [direnv][] to load the environment automatically
- source this file manually from your shell
- or use it as a reference for what to put in your preferred rc files

[direnv]: https://direnv.net/

## Development Environment

If you use a different development environment or editor set up, please document
it here!

### IntelliJ IDEA

Download the community edition of [IntelliJ IDEA](https://www.jetbrains.com/idea/)
and set up a new project.

### Emacs

You can use the [metals][] Scala language server together with [lsp-mode][] for
a nice IDE experience in the world's best lisp driven operating system.

#### Install `metals-emacs`

##### Arch

Using yay to install from AUR:

```sh
yay -Syu metals
```

#### Doom Emacs

[Doom Emacs][doom-emacs] streamlines configuration and installation:

Edit your [~/.doom.d/init.el](~/.doom.d/init.el), to uncomment `scala` and
configure it use lsp:

```elisp
       (scala              ; java, but good
        +lsp)
```

Run `doom sync` and restart. That's it.

If you hit any snags, you might also consult [this
writeup][writeup]

[doom-emacs]: https://github.com/hlissner/doom-emacs
[metals]: https://scalameta.org/metals/
[lsp-mode]: https://github.com/emacs-lsp/lsp-mode
[writeup]: https://siawyoung.com/blog/code/2020-02-06-installing-metals-emacs-doom

#### Vanilla Emacs

For installation and configuration in vanilla emacs, see
https://scalameta.org/metals/docs/editors/emacs.html

## Testing

### Unit tests

Run the units

```sh
make test
```

### Integration tests

#### Installing Dependencies

We use [mdx](https://github.com/realworldocaml/mdx) for CLI integration tests.

Here is a platform agnostic installation recipe:

```sh
# Install opam
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
# Install mdx
opam install mdx
```

For alternative installation methods for opam, see https://opam.ocaml.org/doc/Install.html

#### Running the tests

To build a fresh executable and run all the integration tests, execute

```sh
make integration
```

For more details on running the integration tests, see [./test/tla/cli-integration-tests.md](./test/tla/cli-integration-tests.md).

### Continuous Integration

We run continuous integration tests using [GitHub actions](https://github.com/informalsystems/apalache/actions).

The CI configuration is located in
[.github/workflows/main.yml](.github/workflows/main.yml).

## Changelog

Every non-trivial PR must update the [change log](./CHANGES.md).

Changes for a given release should be split between the four sections: Breaking
Changes, Features, Improvements, Bug Fixes.

## Releases

You must have release-me installed and configured with a token. See
https://pypi.org/project/release-me/

Assuming the version to be released is `l.m.n`, as per semantic versioning, the
current release process is as follows:

### Prepare the release

- [ ] Create a new feature branch, `release-l.m.n` and check it out
- [ ] Update [CHANGES.md](./CHANGES.md), adding the heading `## l.m.n` over the
      unreleased changes.
- [ ] Copy this section into a new file named `./script/release-l.m.n.txt`
- [ ] Mark the version as RELEASE via `mvn versions:set -DnewVersion=l.m.n-RELEASE`
- [ ] Commit the changes: `git add . && git commit -m "Prepare for release l.m.n"`
- [ ] Open a PR merging the feature branch into `develop`. Get it merged.
- [ ] Open a PR to merge `unstable` into `master`, titling it `Release l.m.n`

### Cut the release

When the PR is merged into `master`:

- [ ] Checkout `master`
- [ ] Sync with upstream via`git pull origin master`
- [ ] Build the artifact with `make`
- [ ] Post the relese with `./script/release vl.m.n ./scripts/release-l.m.n.txt`
- [ ] Update the download links at https://github.com/informalsystems/apalache/blob/gh-pages/_config.yml#L7

### Advance the version on unstable

- [ ] Checkout `unstable`
- [ ] Run `mvn --batch-mode release:update-versions -DautoVersionSubmodules=true -DdevelopmentVersion=l.m.(n+1)-SNAPSHOT`
- [ ] Commit the chnages `git add . && git commit -m "Bump version to l.m.(n+1)-SNAPSHOT" && git push`

### Announce the relesae

- [ ] Post a notification to the (internal) `#releases` slack channel.

[Github Issue]: https://github.com/informalsystems/apalache/issues
[rfc]: https://en.wikipedia.org/wiki/Request_for_Comments
[adr]: https://en.wikipedia.org/wiki/Architectural_decision
[draft pull request]: https://github.blog/2019-02-14-introducing-draft-pull-requests/
