# TLC CLI Integration Tests

The code blocks in this file use [mdx](https://github.com/realworldocaml/mdx) to
run integration tests of the Apalache CLI interface.

To run these tests, execute the [../mdx-test.py](../mdx-test.py) script with no
arguments.

We include several tests for TLC, to test the integration of the Apalache
modules and TLC.

## How to write a test

See [cli-integration-tests.md](./cli-integration-tests.md).

## How to run tests

(From the project root.)

### Run all the tests in this file

<!-- $MDX skip -->
```sh
test/mdx-test.py
```

### Run a single test

Each section, demarcated by headings, can be run selectively by supplying an
argument that matches the heading.

E.g., to run just the test for TLC help, run

<!-- $MDX skip -->
```sh
test/mdx-test.py "TLC prints help"
```

**NOTE**: This only runs code blocks directly in the named section, and will not
include execution of blocks in nested subsections.

### Run all tests in sections matching a pattern

The matching is based on (perl) pattern matching. E.g., you can run all the
tests in sections that include the string `"executable"` in their headings with

<!-- $MDX skip -->
```sh
test/mdx-test.py executable
```

## test environment

### working directory

```sh
$ pwd | grep -o test/tla
test/tla
```

## downloading TLC

### tla2tools.jar is available

Since `tla2tools.jar` has been changing under the same version number for over
four years, we download it every time. This goes against [Semantic
Versioning](https://semver.org/), but we cannot enforce good practices at
other organizations.

```sh
$ wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
...
```

### TLC prints help

```sh
$ (java -cp tla2tools.jar tlc2.TLC -help 2>&1 | grep -q 'The model checker') && echo "OK"
...
OK
```

### TLC works on TestVariants.tla

```sh
$ java -cp tla2tools.jar:../../src/tla/ tlc2.TLC -config test.cfg TestVariants.tla
...
Model checking completed. No error has been found.
...
```

### TLC works on TestApalache.tla

```sh
$ java -cp tla2tools.jar:../../src/tla/ tlc2.TLC -config test.cfg TestApalache.tla
...
Model checking completed. No error has been found.
...
```

