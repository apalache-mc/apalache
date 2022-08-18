# ADR-019: Harmonize changelog management

| authors                                | last revised    |
| -------------------------------------- | --------------: |
| Shon Feder                             | 2022-05-06      |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

In the context of maintaining a changelog to communicate salient changes about
our software, facing the friction caused by frequent merge conflicts in our
`UNRELEASED` changelog, we decided to find a lightweight, conflict free,
changelog process in order to achieve a smoother development process. We have
accepted the development cost and learning curve required by adopting a new
process.

## Context

We maintain a [changelog](https://keepachangelog.com/en/1.0.0/)

> to make it easier for users and contributors to see precisely what notable
> changes have been made between each release (or version) of the project.

Any changeset that introduces observable changes to the behavior of our software
should include additions to the changelog.  Currently, [additions are made](https://github.com/informalsystems/apalache/blob/60e6a14d451cb67c93dfd29cffd0cc0eb9d7922d/CONTRIBUTING.md#changelog) by
updating the `UNRELEASED.md` file. The changes recorded there are then added to
the `CHANGES.md` file during our automated release process.

This process creates a race condition over `UNRELEASED.md` between any
concurrent pull requests. This consequently results in developers constantly
having to resolve merge conflicts. This busy-work slows down development and
adds no value.

## Options

We now enumerate and consider the various options we've conceived for addressing
this problem.

With the exception of option (0), all of the following options would resolve the
problem of merge conflicts and could be integrated into our existing automated
deployment pipeline.  However each option has different costs w/r/t
dependencies, processes, and learning curve.

All of the following options will likely require ongoing maintenance, even
option (0): this is because we already have a set of scripts that manage our
changelog entries in order to support our fully automated releases. So this is
not a space where we are introducing automation for the first time, but is
instead a situation where we are changing an existing automated system.

### 0. Don't change anything

We could do nothing. Developers would continue to resolve changelog conflicts manually.

#### Pros

- Requires no development time on a solution.
- Would require no additional maintenance.

#### Cons

- We'll continue having developer slow-down and busy work when merge conflicts arise.

### 1. Use one of the automated changelog generators

There is a [superabundance](https://github.com/search?q=changelog+auto) of tools
for automatically generating changelogs. These tools extract changelogs from
various different sources such as commit messages, issues, or pull requests.
    
#### Pros

- Requires no new development
- Would eliminate the need to add changelog entries in a separate file

#### Cons

- Developers have to learn the annotation format required by the tool, and they
  have to remember to deploy it in their commits/PRs/issues.
- Infrastructure maintainers have to learn how to configure and maintain the tool.
- We pickup a dependency external to both the company and our project
- Changelogs are meant to communicate a very specific kind of information to a
  specific audience. Git commit messages, pull requests, and issues are for
  communicating quite different information to an entirely different audience.
  Requiring that these communication channels be overloaded risks degrading the
  quality of communications in all the conflated channels.
  - However, it's possible we could work out some conventions to add empty
    commits or designate special PR labels to work around this interference?


### 2. Use Unclog

[@thanethomson](https://github.com/thanethomson) has written the [unclog][] utility, which is used in both
[informalsystems/tendermint-rs][] and [informalsystems/ibc-rs][]. The tool
stores changelog entries in a directory structure, with each entry in its own
file, ensuring merge conflicts can't arise. 

Entries are added via the CLI. E.g.:

```sh
unclog add --id some-new-feature \
  --issue 23 \
  --section breaking-changes \
  --message "Some *new* feature"
```

If the `--messages` argument is omitted, it will open your configured editor for
authoring the message.

The tool has subcommands to generate and update the `CHANGES.md`, and it supports
a variety of options via its TOML configuration.

[unclog]: https://github.com/informalsystems/unclog
[informalsystems/tendermint-rs]: https://github.com/informalsystems/tendermint-rs
[informalsystems/ibc-rs]: https://github.com/informalsystems/ibc-rs

#### Pros

- Requires no new development
- It is developed internally to informal

#### Cons

- Adds cognitive and procedural overhead to adding changelog entries
- Would add a rust dependency to our devenv
- Requires external contributors to either install a CLI tool or figure out a
  relatively complex file and folder structure to add changelog entries

### 3. Use a custom git merge driver

If we wrote a [custom git merge driver](https://git-scm.com/docs/gitattributes#_defining_a_custom_merge_driver) to work on the simple changelog format we
could continue our current practice, and just fall back to the custom merge
driver in case of merge conflicts.

#### Pros

- Allows us to keep our current process of simply updating a markdown file,
  with which, moreover, most devs are already familiar

#### Cons

- Could require external dependencies to be installed, depending on
  implementation.
- It's not possible to configure custom merge drivers for github, so we'd either
  need to develop a github action or bot to monitor for merge conflicts in the
  changelog and merge them automatically, or devs would be back to having to
  resolve merge conflicts locally.

### 4. Write some lightweight tooling

We could author some simple tooling that would capture the core behavior of
`unclog`, using files in directories, but neither require external dependencies
nor knowledge of a new CLI.

#### Pros

- No new tooling to learn
- No external dependencies to integrate

#### Cons

- Would require some development time (I estimate approx. 1 day, see the design
  sketch below for details on the implementation)
- Would require contributors to understand the folder structure

## Solution

We have opted for option 4. Despite the added cost of development, we think the
simplicity of use and maintenance will offset the development cost.

### Design

We will introduce a new directory tree to the project:

```sh
.unreleased/
├── breaking-changes/
├── bug-fixes/
├── documentation/
└── features/
```

Each change will be added as a single markdown file in the appropriate
directory.

Two `sbt` targets will be added to facilitate our continuous deployment:

- `releaseNotes`, merges the unreleased notes into a single new file of the expected format in our `target` directory. This can be used for upload to github releases.
- `changeLog` updates `CHANGES.md` by prepending the output of `releaseNotes`. It then removes all notes
  from the `.unreleased` directory so that the next iteration of development starts from a clean slate.

## Consequences

TBD
<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->
