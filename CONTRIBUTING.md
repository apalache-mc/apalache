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
    - [Testing](#testing)
    - [Changelog](#changelog)
    - [Releases](#releases)

<!-- markdown-toc end -->

## Decision Making

<!-- TODO(QUESTION): Do we want this much overhead to contributions? -->

When contributing to the project, the following process leads to the best chance
of landing changes:

All work on the code base should be motivated by a [Github Issue][]. The issue
helps capture the problem we're trying to solve and allows for early feedback.

Once the issue is created, maintainers may request more detailed documentation
in the form of a [Request for Comment (RFC)][rfc] or [Architectural Decision
Record (ADR)][adr].

Discussion at the RFC stage will build collective understanding of the
dimensions of the problem and help structure conversations around trade-offs.

When the problem is well understood but the solution leads to large structural
changes to the code base, these changes should be proposed in the form of an
ADR. The ADR will help build consensus on an overall strategy to ensure the code
base maintains coherence in the larger context. If you are not comfortable with
writing an ADR, you can open a less-formal issue and the maintainers will help
you turn it into an ADR.

When the problem and proposed solution are well understood, implementation can
begin by opening a [pull request](#making-a-pull-request).

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

## Testing

TODO

## Changelog

Every non-trivial PR must update the [change log](./CHANGES.md).

Changes for a given release should be split between the four sections: Breaking
Changes, Features, Improvements, Bug Fixes.

## Releases

TODO

[Github Issue]: https://github.com/informalsystems/apalache/issues
[rfc]: https://en.wikipedia.org/wiki/Request_for_Comments
[adr]: https://en.wikipedia.org/wiki/Architectural_decision
[draft pull request]: https://github.blog/2019-02-14-introducing-draft-pull-requests/
