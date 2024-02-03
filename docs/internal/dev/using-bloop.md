# Developing with bloop

[Bloop](https://scalacenter.github.io/bloop/) is a build server that can yield
lightning fast incremental builds of Scala projects.

It is used by [Scala Metals](https://scalameta.org/metals/), but is also very
useful as a standalone to save devs from the pain of `mvn`.

## Run apalache

To run Apalache via bloop 

```sh
bloop run tool
```

Pass CLI arguments after a `--`, e.g.

```sh
bloop run tool -- check $PWD/<file>
```


Where `<file>` is the path to the file you want to check (note that the path has
to be absolute, as there currently no way to specify the cwd for bloop commands).

You can also run Apalache while watching files, so that any new changes to
source files will trigger an incremental rebuild:

```sh
bloop run tool -w -- check <file>
```

## Build a project

You can list all the projects that can be built with 

```sh
$ bloop projects
apalache
apalache-pkg
apalache-pkg-test
apalache-test
infra
infra-test
tla-assignments
tla-assignments-test
tla-bmcmt
tla-bmcmt-test
tla-io
tla-io-test
tla-pp
tla-pp-test
tla-types
tla-types-test
tlair
tlair-test
tool
tool-test
```

Compile a particular project with:

```sh
$ bloop compile <project> [-w]
```

The optional `-w` flag will set bloop to watch the source files and recompile
incrementally on changes.

## Run tests

You can run the tests for a project with

```sh
$ bloop test <project> [-w] [-o path.to.TestSuite]
```
