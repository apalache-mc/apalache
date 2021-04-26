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

### parse LocalDefClash576 succeeds

```sh
$ apalache-mc parse LocalDefClash576.tla | sed 's/I@.*//'
...
EXITCODE: OK
...
```

### parse LocalInstanceClash576 succeeds

```sh
$ apalache-mc parse LocalInstanceClash576.tla | sed 's/I@.*//'
...
EXITCODE: OK
...
```

### parse Select575 succeeds

```sh
$ apalache-mc parse Select575.tla | sed 's/I@.*//'
...
EXITCODE: OK
...
```

### parse Rec12 succeeds

```sh
$ apalache-mc parse Rec12.tla | sed 's/I@.*//'
...
EXITCODE: OK
...
```

### parse Annotations succeeds

```sh
$ apalache-mc parse Annotations.tla | sed 's/I@.*//'
...
EXITCODE: OK
...
```

### test TestGen finds an example

This simple test demonstrates how to test a spec by isolating the input with
generators.

```sh
$ apalache-mc test TestGen.tla Prepare Test Assertion | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an example. Check counterexample.tla.
...
```

## running the check command

#### check factorization find a counterexample

```sh
$ apalache-mc check --length=2 --inv=Inv factorization.tla | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an error
...
```

### check Fix531.tla reports no error: regression for issue 531

```sh
$ apalache-mc check --length=1 Fix531.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check UnchangedExpr471.tla reports no error: regression for issue 471

```sh
$ apalache-mc check --cinit=ConstInit --length=1 UnchangedExpr471.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check ExistTuple476.tla reports no error: regression for issue 476

```sh
$ apalache-mc check --length=1 ExistTuple476.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check InvSub for SafeMath reports no error: regression for issue 450

```sh
$ apalache-mc check --length=1 --inv=InvSub SafeMath.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check InvAdd for SafeMath reports no error: regression for issue 450

```sh
$ apalache-mc check --length=1 --inv=InvAdd SafeMath.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Fix365_ExistsSubset succeeds: regression for issue 365

```sh
$ apalache-mc check --length=10 Fix365_ExistsSubset.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Fix365_ExistsSubset2 succeeds: regression for issue 365

```sh
$ apalache-mc check --length=10 Fix365_ExistsSubset2.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Fix365_ExistsSubset3 succeeds: regression for issue 365

```sh
$ apalache-mc check --length=10 Fix365_ExistsSubset3.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

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

### check Rec2.tla succeeds

```sh
$ apalache-mc check --length=5 --inv=Inv Rec2.tla | sed 's/I@.*//'
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

### check Rec5.tla succeeds

```sh
$ apalache-mc check --length=5 --inv=Inv Rec5.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Rec6.tla succeeds

```sh
$ apalache-mc check --length=5 --inv=Inv Rec6.tla | sed 's/I@.*//'
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
$ apalache-mc check --length=3 --inv=Inv Rec9.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Rec10.tla fails without UNROLL_DEFAULT_Fact

```sh
$ apalache-mc check Rec10.tla | sed 's/[IEW]@.*//'
...
Input error (see the manual): Recursive operator Fact requires an annotation UNROLL_DEFAULT_Fact. See: https://apalache.informal.systems/docs/apalache/principles.html#recursion
...
EXITCODE: ERROR (99)
```

### check Rec11.tla fails without UNROLL_TIMES_Fact

```sh
$ apalache-mc check Rec11.tla | sed 's/[IEW]@.*//'
...
Input error (see the manual): Recursive operator Fact requires an annotation UNROLL_TIMES_Fact. See: https://apalache.informal.systems/docs/apalache/principles.html#recursion
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

### check Rec13.tla succeeds

```sh
$ apalache-mc check --inv=Inv Rec13.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```


### check ExistsAsValue.tla succeeds

```sh
$ apalache-mc check --inv=Inv ExistsAsValue.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check reorderTest.tla MayFail succeeds: fixed SMT fails under SMT-based assignment finding

```sh
$ apalache-mc check --next=MayFail --tuning=reorderTest.properties reorderTest.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check reorderTest.tla MustFail fails

```sh
$ apalache-mc check --next=MustFail reorderTest.tla
...
EXITCODE: ERROR (99)
[99]
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

### check NonNullaryLet succeeds: regression for issue 429

```sh
$ apalache-mc check NonNullaryLet.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check CaseNoOther succeeds

```sh
$ apalache-mc check CaseNoOther.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check CaseNoOtherBool succeeds

```sh
$ apalache-mc check CaseNoOtherBool.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Callback.tla succeeds

`Callback.tla` demonstrates that one can implement non-determinism with the existential operator and use a callback to
do an assignment to a variable. As it requires tricky operator inlining, here is the test.

```sh
$ apalache-mc check Callback.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check SimpT1 succeeds

This test was moved from a unit test of SymbTransGenerator. The goal of the test is to check that symbolic transitions
are extracted from the spec. Hence, we run model checking only against the initial states.

```sh
$ apalache-mc check --length=0 SimpT1.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check Selections succeeds

```sh
$ apalache-mc check Selections.tla | sed 's/I@.*//'
...
Selections.tla:16:18-16:27: Missing assignments to: z
...
EXITCODE: ERROR (99)
```

### check test1 succeeds

```sh
$ apalache-mc check test1.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
```

### check ITE_CASE succeeds

```sh
$ apalache-mc check ITE_CASE.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (99)
```

### check Deadlock712 succeeds

This test shows that Apalache may miss a deadlock, as discussed in issue 712.
Once this is fixed, Apalache should find a deadlock.

```sh
$ apalache-mc check Deadlock712.tla | sed 's/I@.*//'
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

### configure via TLC config with SPECIFICATION and fairness

```sh
$ apalache-mc check --config=Config4.cfg Config.tla | sed 's/[IEW]@.*//'
...
  > Config4.cfg: Loading TLC configuration
...
  > Config4.cfg: Using SPECIFICATION Spec4
...
  > Set the initialization predicate to Init2
  > Set the transition predicate to Next2
  > Set an invariant to Inv2
...
The outcome is: NoError
...
```

### configure via TLC config with SPECIFICATION and fairness

```sh
$ apalache-mc check --config=Config5.cfg Config.tla | sed 's/[IEW]@.*//'
...
  > Config5.cfg: Loading TLC configuration
...
  > Config5.cfg: Using SPECIFICATION Spec5
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
Configuration error (see the manual): Found a cyclic dependency among operators: B, A, C
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

## testing the slicer of symbolic transitions in TransitionFinderPass

### check Slicer1

```sh
$ apalache-mc check --inv=Inv Slicer1.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
```

### check Slicer2

```sh
$ apalache-mc check --inv=Inv Slicer2.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
```

### check Slicer3

```sh
$ apalache-mc check --inv=Inv Slicer3.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
```

### check Slicer4

```sh
$ apalache-mc check --inv=Inv Slicer4.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
```

### check Slicer5

```sh
$ apalache-mc check --inv=Inv Slicer5.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
```

## running the typecheck command

### typecheck ExistTuple476.tla reports no error: regression for issues 476 and 482

```sh
$ apalache-mc typecheck ExistTuple476.tla | sed 's/I@.*//'
...
 > All expressions are typed
...
Type checker [OK]
...
```

### typecheck CarTalkPuzzleTyped.tla

```sh
$ apalache-mc typecheck CarTalkPuzzleTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck CigaretteSmokersTyped.tla

```sh
$ apalache-mc typecheck CigaretteSmokersTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck GameOfLifeTyped.tla

```sh
$ apalache-mc typecheck GameOfLifeTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck MissionariesAndCannibalsTyped.tla

```sh
$ apalache-mc typecheck MissionariesAndCannibalsTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck PrisonersTyped.tla

```sh
$ apalache-mc typecheck PrisonersTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck QueensTyped.tla succeeds

We use `FunAsSeq` to convert a function to a sequence.
This test should now pass.

```sh
$ apalache-mc typecheck QueensTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck SlidingPuzzlesTyped.tla

```sh
$ apalache-mc typecheck SlidingPuzzlesTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck TwoPhaseTyped.tla

```sh
$ apalache-mc typecheck TwoPhaseTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
PASS #2: Terminal
Type checker [OK]
...
EXITCODE: OK
```

### typecheck FunctionsTyped.tla

```sh
$ apalache-mc typecheck FunctionsTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck FiniteSetsExtTyped.tla

```sh
$ apalache-mc typecheck FiniteSetsExtTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck HourClockTyped.tla

```sh
$ apalache-mc typecheck HourClockTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck Channel.tla

```sh
$ apalache-mc typecheck Channel.tla | sed 's/[IEW]@.*//'
...
Typing input error: Expected a type annotation for VARIABLE chan
...
EXITCODE: ERROR (99)
```

### typecheck ChannelTyped.tla

```sh
$ apalache-mc typecheck ChannelTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck PascalTriangle.tla

```sh
$ apalache-mc typecheck PascalTriangle.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck AnnotationsAndInstances592.tla

```sh
$ apalache-mc typecheck AnnotationsAndInstances592.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck AnnotationsAndSubstitutions596.tla

```sh
$ apalache-mc typecheck AnnotationsAndSubstitutions596.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck Except617.tla

```sh
$ apalache-mc typecheck Except617.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck Unchanged660.tla

```sh
$ apalache-mc typecheck Unchanged660.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are great!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck UntypedConst.tla

```sh
$ apalache-mc typecheck UntypedConst.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
Typing input error: Expected a type annotation for CONSTANT N
...
EXITCODE: ERROR (99)
```

### typecheck UntypedVar.tla

```sh
$ apalache-mc typecheck UntypedVar.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
Typing input error: Expected a type annotation for VARIABLE x
...
EXITCODE: ERROR (99)
```

## Running the config command

### config --enable-stats=false

```sh
$ apalache-mc config --enable-stats=false | sed 's/[IEW]@.*//'
...
Statistics collection is OFF.
...
EXITCODE: OK
```

### config --enable-stats=true

```sh
$ apalache-mc config --enable-stats=true | sed 's/[IEW]@.*//'
...
Statistics collection is ON.
...
EXITCODE: OK
```

