# Apalache CLI Integration Tests

The code blocks in this file use [mdx](https://github.com/realworldocaml/mdx) to
run integration tests of the Apalache CLI interface.

To run these tests, execute the [../mdx-test.py](../mdx-test.py) script with no
arguments.

## How to write a test

Any `sh` code block will be run as a test.

The test executes the command following a `$`. The command is expected to
produce the output on the subsequent lines of the code block.

Some tips:

- Use `...` to omit irrelevant lines in output. This is useful for
  nondeterministic output or to hide noise.
- Specify a non-zero return code `n` by adding `[n]` on a line by itself after
  the output.
- Pipe into filters to get arbitrary control of the expected output.

The usual flow is:

1. Write a failing test that executes the command to be run.
2. Run the test (see below).
3. Check that the corrected output is what you expect, then run `make promote`,
   to copy the output back into this file.
4. Replace any non-essential lines with `...`.

See the documentation on `mdx` for more features and flexibility.

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

E.g., to run just the test for the `version` command, run

<!-- $MDX skip -->
```sh
test/mdx-test.py "executable prints version"
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

## executing the binary

### executable prints version

```sh
$ apalache-mc version
...
EXITCODE: OK
```

### executable prints help

```sh
$ apalache-mc help
...
EXITCODE: OK
```

## running the parse command

This command parses a TLA+ specification with the SANY parser.

### parse Rec12 succeeds

```sh
$ apalache-mc parse Rec12.tla | sed 's/I@.*//'
...
EXITCODE: OK
...
```

## running the check command


### check Bug20201118 succeeds: regression for issue 333

```sh
$ apalache-mc check --length=10 --init=Init --next=Next --inv=Inv Bug20201118.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Fix333 succeeds: another regression for issue 333

```sh
$ apalache-mc check --length=2 --init=Init --next=Next --inv=Inv Fix333.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Bug20190118 succeeds

```sh
$ apalache-mc check --length=1 --init=Init --next=Next --inv=Inv Bug20190118.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check mis.tla succeeds

```sh
$ apalache-mc check --length=5 --inv=IsIndependent mis.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check mis_bug.tla errors

```sh
$ apalache-mc check --length=5 --inv=IsIndependent mis_bug.tla | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an error
...
```


### check ast.tla succeeds

```sh
$ apalache-mc check --length=5 ast.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check pr.tla suceeds

```sh
$ apalache-mc check --length=2 pr.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check EWD840.tla succeeds

```sh
$ apalache-mc check --length=5 --inv=Inv EWD840.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Paxos.tla succeeds

```sh
$ apalache-mc check --length=5 --inv=Inv Paxos.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Bug20190118 succeeds

```sh
$ apalache-mc check --length=1 Bug20190118.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Bug20190921 succeeds

```sh
$ apalache-mc check --length=5 --cinit=CInit Bug20190921.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Counter.tla errors

```sh
$ apalache-mc check --length=10 --inv=Inv Counter.tla | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an error
...
```

### y2k.tla

#### check y2k with length 20 and ConstInit errors

```sh
$ apalache-mc check --length=20 --inv=Safety --cinit=ConstInit y2k_cinit.tla  | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an error
...
```

#### check y2k with length 19 succeeds

```sh
$ apalache-mc check --length=19 --inv=Safety y2k_instance.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

#### check y2k with length 30 errors

```sh
$ apalache-mc check --length=30 --inv=Safety y2k_instance.tla | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an error
...
```

### check Counter.tla errors

```sh
$ apalache-mc check --length=10 --inv=Inv Counter.tla | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an error
...
```

### check NatCounter.tla errors

```sh
$ apalache-mc check --length=10 --inv=Inv NatCounter.tla  | sed 's/I@.*//'
...
The outcome is: Error
...
```

### check NeedForTypesWithTypes.tla succeeds

```sh
$ apalache-mc check --length=10 --cinit=ConstInit --inv=Inv NeedForTypesWithTypes.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check HandshakeWithTypes.tla with length 4 succeeds

```sh
$ apalache-mc check --length=4 --inv=Inv HandshakeWithTypes.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check HandshakeWithTypes.tla with lengh 5 deadlocks

```sh
$ apalache-mc check --length=5 --inv=Inv HandshakeWithTypes.tla | sed 's/I@.*//'
...
The outcome is: Deadlock
...
```

### check trivial violation of FALSE invariant

```sh
$ apalache-mc check --length=2 --inv=Inv Bug20200306.tla | sed 's/I@.*//'
...
The outcome is: Error
...
```

### check Init without an assignment fails

```sh
$ apalache-mc check --length=1 --inv=Inv Assignments20200309.tla
...
EXITCODE: ERROR (99)
[99]
```

### check Inline.tla suceeds

```sh
$ apalache-mc check --length=5 Inline.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Rec1.tla succeeds

```sh
$ apalache-mc check --length=5 --inv=Inv Rec1.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Rec3.tla succeeds
```sh
$ apalache-mc check --length=10 --inv=Inv Rec3.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Rec4.tla succeeds

Unfolding Fibonacci numbers

```sh
$ apalache-mc check --length=10 --inv=Inv Rec4.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Rec8.tla succeeds

```sh
$ apalache-mc check --length=10 --inv=Inv Rec8.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Rec9.tla succeeds

```sh
$ apalache-mc check --length=5 --inv=Inv Rec9.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Rec10.tla fails without UNROLL_DEFAULT_Fact

```sh
$ apalache-mc check Rec10.tla | sed 's/[IEW]@.*//'
...
Input error (see the manual): Recursive operator Fact requires an annotation UNROLL_DEFAULT_Fact. See: https://github.com/informalsystems/apalache/blob/unstable/docs/manual.md#recursion
...
EXITCODE: ERROR (99)
```

### check Rec11.tla fails without UNROLL_TIMES_Fact

```sh
$ apalache-mc check Rec11.tla | sed 's/[IEW]@.*//'
...
Input error (see the manual): Recursive operator Fact requires an annotation UNROLL_TIMES_Fact. See: https://github.com/informalsystems/apalache/blob/unstable/docs/manual.md#recursion
...
EXITCODE: ERROR (99)
```

### check Rec12.tla works with Init

```sh
$ apalache-mc check --inv=Inv Rec12.tla | sed 's/[IEW]@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Rec12.tla produces an error with Init2

```sh
$ apalache-mc check --init=Init2 --inv=Inv Rec12.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
EXITCODE: OK
```


### check ExistsAsValue.tla succeeds

```sh
$ apalache-mc check --inv=Inv ExistsAsValue.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Empty.tla fails

```sh
$ apalache-mc check Empty.tla
...
EXITCODE: ERROR (99)
[99]
```

### check HourClock.tla without Init fails

```sh
$ apalache-mc check --init=NonExistantInit HourClock.tla
...
EXITCODE: ERROR (99)
[99]
```

### check HourClock.tla without Next fails

```sh
$ apalache-mc check --next=NonExistantNext HourClock.tla
...
EXITCODE: ERROR (99)
[99]
```

### check HourClock.tla without Inv fails

```sh
$ apalache-mc check --inv=NonExistantInv HourClock.tla
...
EXITCODE: ERROR (99)
[99]
```

### check Callback.tla succeeds

`Callback.tla` demonstrates that one can implement non-determinism with
the existential operator and use a callback to do an assignment to a variable.
As it requires tricky operator inlining, here is the test.

```sh
$ apalache-mc check Callback.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check use of TLA_PATH for modules in child directory succeeds

```sh
$ TLA_PATH=./tla-path-tests apalache-mc check ./tla-path-tests/ImportingModule.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

## configure the check command

Testing various flags that are set via command-line options and the TLC
configuration file. The CLI has priority over the TLC config. So we have to
test that it all works together.

### configure default Init and Next

```sh
$ apalache-mc check Config.tla | sed 's/I@.*//'
...
  > Command line option --init is not set. Using Init
  > Command line option --next is not set. Using Next
...
  > Set the initialization predicate to Init
  > Set the transition predicate to Next
...
The outcome is: NoError
...
```

### configure an invariant via CLI

```sh
$ apalache-mc check --inv=Inv Config.tla | sed 's/I@.*//'
...
  > Set an invariant to Inv
...
The outcome is: NoError
...
```

### configure all params via CLI

```sh
$ apalache-mc check --init=Init1 --next=Next1 --inv=Inv Config.tla | sed 's/I@.*//'
...
  > Set the initialization predicate to Init1
  > Set the transition predicate to Next1
  > Set an invariant to Inv
...
The outcome is: Error
...
```

### configure via TLC config

```sh
$ apalache-mc check --config=Config1.cfg Config.tla | sed 's/[IEW]@.*//'
...
  > Config1.cfg: Loading TLC configuration
...
  > Config1.cfg: PROPERTY AwesomeLiveness is ignored. Only INVARIANTS are supported.
...
  > Set the initialization predicate to Init1
  > Set the transition predicate to Next1
  > Set an invariant to Inv1
...
The outcome is: NoError
...
```

### configure via TLC config and override it via CLI

```sh
$ apalache-mc check --config=Config1.cfg --init=Init2 --next=Next2 Config.tla | sed 's/[IEW]@.*//'
...
  > Config1.cfg: Loading TLC configuration
...
  > Set the initialization predicate to Init2
  > Set the transition predicate to Next2
  > Set an invariant to Inv1
...
The outcome is: Error
...
```

### configure missing property in TLC config 

```sh
$ apalache-mc check --config=Config3.cfg Config.tla | sed 's/[IE]@.*//'
...
  > Config3.cfg: Loading TLC configuration
...
Configuration error (see the manual): Operator NoLiveness not found (used as a temporal property)
...
EXITCODE: ERROR (99)
```

### configure via TLC config with SPECIFICATION

```sh
$ apalache-mc check --config=Config2.cfg Config.tla | sed 's/[IEW]@.*//'
...
  > Config2.cfg: Loading TLC configuration
...
  > Config2.cfg: Using SPECIFICATION Spec2
...
  > Set the initialization predicate to Init2
  > Set the transition predicate to Next2
  > Set an invariant to Inv2
...
The outcome is: NoError
...
```

### configure complains about circular dependencies

```sh
$ apalache-mc check ConfigUnsorted.tla | sed 's/[IEW]@.*//'
...
Configuration error (see the manual): Circular definition dependency detected
...
EXITCODE: ERROR (99)
```

### configure via TLC config and assign constants

```sh
$ apalache-mc check --config=ConfigParams.cfg ConfigParams.tla | sed 's/[IEW]@.*//'
...
  > ConfigParams.cfg: Loading TLC configuration
  > Using the init predicate Init from the TLC config
  > Using the next predicate Next from the TLC config
  > ConfigParams.cfg: found INVARIANTS: Inv
  > Set the initialization predicate to Init
  > Set the transition predicate to Next
  > Set an invariant to Inv
  > Replaced CONSTANT MyInt with 42
  > Replaced CONSTANT MyStr with "hello"
  > Replaced CONSTANT MyModelValue1 with "ModelValue_Model1"
  > Replaced CONSTANT MyModelValue2 with "ModelValue_Model2"
  > Replaced CONSTANT MySet with {1, 2, 3}
...
The outcome is: NoError
...
```

### configure via TLC config and replace operators

```sh
$ apalache-mc check --config=ConfigReplacements2.cfg ConfigReplacements.tla | sed 's/[IEW]@.*//'
...
  > ConfigReplacements2.cfg: Loading TLC configuration
  > Using the init predicate Init from the TLC config
  > Using the next predicate Next from the TLC config
  > ConfigReplacements2.cfg: found INVARIANTS: Inv
  > Set the initialization predicate to Init
  > Set the transition predicate to Next
  > Set an invariant to Inv
  > Replaced operator Value with OVERRIDE_Value
...
The outcome is: NoError
...
```

### configure via TLC config and replace operators helps us to keep the invariant

```sh
$ apalache-mc check --inv=Inv ConfigReplacements.tla | sed 's/[IEW]@.*//'
...
  > ConfigReplacements.cfg: Loading TLC configuration
  > No TLC configuration found. Skipping.
...
The outcome is: Error
...
```

## running the typecheck command

### typecheck CarTalkPuzzleTyped.tla

```sh
$ apalache-mc typecheck CarTalkPuzzleTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck CigaretteSmokersTyped.tla

```sh
$ apalache-mc typecheck CigaretteSmokersTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck GameOfLifeTyped.tla

```sh
$ apalache-mc typecheck GameOfLifeTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck MissionariesAndCannibalsTyped.tla

```sh
$ apalache-mc typecheck MissionariesAndCannibalsTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck PrisonersTyped.tla

```sh
$ apalache-mc typecheck PrisonersTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck QueensTyped.tla fails

We are not currently able to typecheck this spec, since we need a way of
coercing functions on integers into sequences, or a way to recognize the former
as subtypes of the latter. This failing test is added to document the current limitation
of the Etc type checkers, and we expect it will be changed into a passing test
once the desired  functionality and added.

```sh
$ apalache-mc typecheck QueensTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
[QueensTyped.tla:41:44-41:61]: Mismatch in argument types. Expected: (Seq(Int)) => Bool
[QueensTyped.tla:41:14-41:63]: Error when computing the type of Solutions
  :-|
Type checker [FAILED]
...
EXITCODE: OK
```

### typecheck SlidingPuzzlesTyped.tla

```sh
$ apalache-mc typecheck SlidingPuzzlesTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck TwoPhaseTyped.tla

```sh
$ apalache-mc typecheck TwoPhaseTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

## running the typecheck command

### typecheck CarTalkPuzzleTyped.tla

```sh
$ apalache-mc typecheck CarTalkPuzzleTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck CigaretteSmokersTyped.tla

```sh
$ apalache-mc typecheck CigaretteSmokersTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck GameOfLifeTyped.tla

```sh
$ apalache-mc typecheck GameOfLifeTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck MissionariesAndCannibalsTyped.tla

```sh
$ apalache-mc typecheck MissionariesAndCannibalsTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck PrisonersTyped.tla

```sh
$ apalache-mc typecheck PrisonersTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck QueensTyped.tla fails

We are not currently able to typecheck this spec, since we need a way of
coercing functions on integers into sequences, or a way to recognize the former
as subtypes of the latter. This failing test is added to document the current limitation
of the Etc type checkers, and we expect it will be changed into a passing test
once the desired  functionality and added.

```sh
$ apalache-mc typecheck QueensTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
[QueensTyped.tla:41:44-41:61]: Mismatch in argument types. Expected: (Seq(Int)) => Bool
[QueensTyped.tla:41:14-41:63]: Error when computing the type of Solutions
  :-|
Type checker [FAILED]
...
EXITCODE: OK
```

### typecheck SlidingPuzzlesTyped.tla

```sh
$ apalache-mc typecheck SlidingPuzzlesTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck TwoPhaseTyped.tla

```sh
$ apalache-mc typecheck TwoPhaseTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeChecker
 > running ETC: Embarrassingly simple Type Checker
   ^_^
  =^_^=
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```
