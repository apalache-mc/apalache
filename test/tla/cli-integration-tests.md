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
```

### executable prints help

```sh
$ apalache-mc help
...
```

### executable responds to JVM_ARGS environment variable

We can set some JVM args and still have the default max heap size supplied.

```sh
$ JVM_ARGS="-Xms1m -XX:+UseSerialGC" apalache-mc version --debug
...
# JVM args: -Xms1m -XX:+UseSerialGC -Xmx4096m
...
```

If we set the max heap size (with `-Xmx`) it will override the default max heap size:

```sh
$ JVM_ARGS="-Xmx16m" apalache-mc version --debug
...
# JVM args: -Xmx16m
...
```

## Running the config command

Enable statistics collection.

### config --enable-stats=true

Test that it is possible to turn on the statistics. Before and after calling
this command, we turn the stats off, so tla2tools do not call home.

```sh
$ mkdir -p $HOME/.tlaplus && echo NO_STATISTICS >$HOME/.tlaplus/esc.txt
$ apalache-mc config --enable-stats=true | sed 's/[IEW]@.*//'
...
Statistics collection is ON.
...
EXITCODE: OK
$ apalache-mc parse Empty.tla | grep '# Usage statistics'
...
# Usage statistics is ON. Thank you!
...
$ grep -q -v NO_STATISTICS $HOME/.tlaplus/esc.txt
$ echo NO_STATISTICS >$HOME/.tlaplus/esc.txt
```

### config --enable-stats=false

Disable statistics collection. We fix the installation id, so we can
distinguish it from normal users. After executing the command, we turn the
statistics off again.

```sh
$ mkdir -p $HOME/.tlaplus
$ echo c1cd000000000000000000000000c1cd >$HOME/.tlaplus/esc.txt
$ apalache-mc config --enable-stats=false | sed 's/[IEW]@.*//'
...
Statistics collection is OFF.
...
EXITCODE: OK
$ apalache-mc parse Empty.tla | grep '# Usage statistics'
...
# Usage statistics is OFF. We care about your privacy.
...
$ head -n 1 $HOME/.tlaplus/esc.txt
NO_STATISTICS
```

## error handling for non-existent files

Ensure that we exit gracefully when commands are called on nonexistent files.

NOTE: We truncate the output to avoid printing the file, making the test
indifferent to the execution environment (including in docker).

```sh
$ for cmd in check parse typecheck transpile; do apalache-mc $cmd nonexistent-file.tla 2>&1 | grep -o -e "EXITCODE: ERROR (255)" -e "Cannot find source file for module"; done
Cannot find source file for module
EXITCODE: ERROR (255)
Cannot find source file for module
EXITCODE: ERROR (255)
Cannot find source file for module
EXITCODE: ERROR (255)
Cannot find source file for module
EXITCODE: ERROR (255)
```

## running the parse command

This command parses a TLA+ specification with the SANY parser.

### parse Empty succeeds

```sh
$ apalache-mc parse Empty.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### parse Empty with --features=rows succeeds

```sh
$ apalache-mc parse --features=rows Empty.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### parse Empty with an unsupported feature fails

```sh
$ apalache-mc parse --features=feature.unsupported Empty.tla 2>&1 | grep 'Failed to parse'
Failed to parse command parse: Incorrect value for option features, got 'feature.unsupported', expected a feature: rows
```

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
```

### parse Annotations succeeds

```sh
$ apalache-mc parse Annotations.tla | sed 's/I@.*//'
...
EXITCODE: OK
...
```

### parse Test1254 succeeds

```sh
$ apalache-mc parse Test1254.tla | sed 's/I@.*//'
...
EXITCODE: OK
...
```

### parse Test1275 succeeds

We have decided to display a warning instead of exiting with an error,
because TLA+ Toolbox generates comments that look like malformed annotations.

```sh
$ apalache-mc parse Test1275.tla | sed 's/W@.*//'
...
[Test1275:5:1-5:12]: Syntax error in annotation -- Unexpected character. Missing ')' or ';'?
...
EXITCODE: OK
...
```

### parse --output=annotations.tla Annotations succeeds

And also check that it actually parses into TLA (see #1079)

```sh
$ apalache-mc parse --output=output.tla Annotations.tla | sed 's/I@.*//'
...
EXITCODE: OK
$ cat output.tla | head
-------------------------------- MODULE output --------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Int;
  *)
  N

$ rm output.tla
```

### parse --output=annotations.json Annotations succeeds

And also check that it actually parses into JSON (see #1079)

```sh
$ apalache-mc parse --output=output.json Annotations.tla | sed 's/I@.*//'
...
EXITCODE: OK
$ cat output.json | head
{
  "name": "ApalacheIR",
  "version": "1.0",
  "description": "https://apalache.informal.systems/docs/adr/005adr-json.html",
  "modules": [
    {
      "kind": "TlaModule",
      "name": "output",
      "declarations": [
        {
$ rm output.json
```

### typecheck --output=output.tla Annotations succeeds

Check that it actually parses into TLA (see #1284)

```sh
$ apalache-mc typecheck --output=output.tla Annotations.tla | sed 's/I@.*//'
...
EXITCODE: OK
$ cat output.tla | head
-------------------------------- MODULE output --------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Int;
  *)
  N

$ rm output.tla
```

### typecheck --output=output.json Annotations succeeds

And also check that it actually parses into JSON (see #1284)

```sh
$ apalache-mc typecheck --output=output.json Annotations.tla | sed 's/I@.*//'
...
EXITCODE: OK
$ cat output.json | head
{
  "name": "ApalacheIR",
  "version": "1.0",
  "description": "https://apalache.informal.systems/docs/adr/005adr-json.html",
  "modules": [
    {
      "kind": "TlaModule",
      "name": "output",
      "declarations": [
        {
$ rm output.json
```

### typecheck can consume own --output

Check that a file produced with `--output` is valid input (see #1281)

```sh
$ apalache-mc typecheck --output=output.json Annotations.tla ; apalache-mc typecheck output.json | sed 's/I@.*//'
...
EXITCODE: OK
$ rm output.json
```

### parse FormulaRefs fails

```sh
$ apalache-mc parse FormulaRefs.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (255)
...
```

### test TestGen finds an example

This simple test demonstrates how to test a spec by isolating the input with generators.

```sh
$ apalache-mc test --features=rows TestGen.tla Prepare Test Assertion | sed 's/I@.*//'
...
The outcome is: Error
Found a violation of the postcondition. Check violation.tla.
...
EXITCODE: ERROR (12)
```

## running the check command

#### check factorization find a counterexample (array-encoding)

```sh
$ apalache-mc check --length=2 --inv=Inv factorization.tla | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an error
...
EXITCODE: ERROR (12)
```

### check Fix531.tla reports no error: regression for issue 531 (array-encoding)

```sh
$ apalache-mc check --length=1 Fix531.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check UnchangedExpr471.tla reports no error: regression for issue 471 (array-encoding)

```sh
$ apalache-mc check --cinit=ConstInit --length=1 UnchangedExpr471.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check ExistTuple476.tla reports no error: regression for issue 476 (array-encoding)

```sh
$ apalache-mc check --length=1 ExistTuple476.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check InvSub for SafeMath reports no error: regression for issue 450 (array-encoding)

```sh
$ apalache-mc check --length=1 --inv=InvSub SafeMath.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check InvAdd for SafeMath reports no error: regression for issue 450 (array-encoding)

```sh
$ apalache-mc check --length=1 --inv=InvAdd SafeMath.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Fix365_ExistsSubset succeeds: regression for issue 365 (array-encoding)

```sh
$ apalache-mc check --length=10 Fix365_ExistsSubset.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Fix365_ExistsSubset2 succeeds: regression for issue 365

```sh
$ apalache-mc check --length=10 Fix365_ExistsSubset2.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Fix365_ExistsSubset3 succeeds: regression for issue 365 (array-encoding)

```sh
$ apalache-mc check --features=rows --length=10 Fix365_ExistsSubset3.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Bug20201118 succeeds: regression for issue 333 (array-encoding)

```sh
$ apalache-mc check --length=10 --init=Init --next=Next --inv=Inv Bug20201118.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Fix333 succeeds: another regression for issue 333 (array-encoding)

```sh
$ apalache-mc check --length=2 --init=Init --next=Next --inv=Inv Fix333.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Bug540 succeeds: regression for issue 540 (array-encoding)

```sh
$ apalache-mc check --features=rows --cinit=CInit Bug540.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Bug593 fails correctly: regression for issue 593 (array-encoding)

```sh
$ apalache-mc check --features=rows Bug593.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (255)
```

### check Bug20190118 succeeds

```sh
$ apalache-mc check --length=1 --init=Init --next=Next --inv=Inv Bug20190118.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check mis.tla succeeds

```sh
$ apalache-mc check --length=5 --inv=IsIndependent mis.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check mis_bug.tla errors

```sh
$ apalache-mc check --length=5 --inv=IsIndependent mis_bug.tla | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an error
...
EXITCODE: ERROR (12)
```


### check ast.tla succeeds

```sh
$ apalache-mc check --length=5 ast.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check pr.tla suceeds (array-encoding)

```sh
$ apalache-mc check --length=2 pr.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check EWD840.tla succeeds

```sh
$ apalache-mc check --length=5 --inv=Inv EWD840.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Paxos.tla succeeds

```sh
$ apalache-mc check --length=5 --inv=Inv Paxos.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Bug20190118 succeeds

```sh
$ apalache-mc check --length=1 Bug20190118.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Bug20190921 succeeds (array-encoding)

```sh
$ apalache-mc check --length=5 --cinit=CInit Bug20190921.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check RangeWithConst succeeds (array-encoding)

```sh
$ apalache-mc check --cinit=CInit --inv=Inv --length=1 RangeWithConst.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check SelectSeqTests succeeds

```sh
$ apalache-mc check --inv=Inv --length=1 SelectSeqTests.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Folds succeeds

```sh
$ apalache-mc check --inv=Inv --length=1 Folds.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check LocalFold succeeds

```sh
$ apalache-mc check --inv=Inv --length=1 LocalFold.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check LocalFold2 succeeds

```sh
$ apalache-mc check --inv=Inv --length=1 LocalFold2.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check FoldSetSeq succeeds

```sh
$ apalache-mc check --inv=Inv --length=1 FoldSetSeq.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check FoldSetSeqBad fails

```sh
$ apalache-mc check --inv=Inv --length=1 FoldSetSeqBad.tla | sed 's/I@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check FoldSetSet succeeds

```sh
$ apalache-mc check --inv=Inv --length=1 FoldSetSet.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check FoldSetSetBad fails

```sh
$ apalache-mc check --inv=Inv --length=1 FoldSetSetBad.tla | sed 's/I@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check FoldSetFun succeeds

```sh
$ apalache-mc check --inv=Inv --length=1 FoldSetFun.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check FoldSetFunBad fails

```sh
$ apalache-mc check --inv=Inv --length=1 FoldSetFunBad.tla | sed 's/I@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check FoldSeqSeq succeeds

```sh
$ apalache-mc check --inv=Inv --length=1 FoldSeqSeq.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check FoldSeqSeqBad fails

```sh
$ apalache-mc check --inv=Inv --length=1 FoldSeqSeqBad.tla | sed 's/I@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check FoldSeqSet succeeds

```sh
$ apalache-mc check --inv=Inv --length=1 FoldSeqSet.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check FoldSeqSetBad fails

```sh
$ apalache-mc check --inv=Inv --length=1 FoldSeqSetBad.tla | sed 's/I@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check FoldSeqFun succeeds

```sh
$ apalache-mc check --inv=Inv --length=1 FoldSeqFun.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check FoldSeqFunBad fails

```sh
$ apalache-mc check --inv=Inv --length=1 FoldSeqFunBad.tla | sed 's/I@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check FoldSetInInit succeeds

```sh
$ apalache-mc check --inv=Inv FoldSetInInit.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Counter.tla errors (array-encoding)

```sh
$ apalache-mc check --length=10 --inv=Inv Counter.tla | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an error
...
EXITCODE: ERROR (12)
```

### y2k.tla

#### check y2k with length 20 and ConstInit errors (array-encoding)

```sh
$ apalache-mc check --length=20 --inv=Safety --cinit=ConstInit y2k_cinit.tla  | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an error
...
EXITCODE: ERROR (12)
```

#### check y2k with length 19 succeeds (array-encoding)

```sh
$ apalache-mc check --length=19 --inv=Safety y2k_instance.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

#### check y2k with length 30 errors (array-encoding)

```sh
$ apalache-mc check --length=30 --inv=Safety y2k_instance.tla | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an error
...
EXITCODE: ERROR (12)
```

### check Counter.tla errors (array-encoding)

```sh
$ apalache-mc check --length=10 --inv=Inv Counter.tla | sed 's/I@.*//'
...
The outcome is: Error
Checker has found an error
...
EXITCODE: ERROR (12)
```

### check NatCounter.tla errors (array-encoding)

```sh
$ apalache-mc check --length=10 --inv=Inv NatCounter.tla  | sed 's/I@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check NeedForTypesWithTypes.tla succeeds

```sh
$ apalache-mc check --length=10 --cinit=ConstInit --inv=Inv NeedForTypesWithTypes.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check HandshakeWithTypes.tla with length 4 succeeds (array-encoding)

```sh
$ apalache-mc check --features=rows --length=4 --inv=Inv HandshakeWithTypes.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check HandshakeWithTypes.tla with length 5 deadlocks (array-encoding)

```sh
$ apalache-mc check --features=rows --length=5 --inv=Inv HandshakeWithTypes.tla | sed 's/I@.*//'
...
The outcome is: Deadlock
...
EXITCODE: ERROR (12)
```

### check HandshakeWithTypes.tla with length 5 passes with --no-deadlock

The option `--no-deadlock` forces the model checker to pass, even if it cannot
extend an execution prefix. See a discussion in
[#1640](https://github.com/informalsystems/apalache/issues/1640).

```sh
$ apalache-mc check --features=rows --length=5 --no-deadlock=1 --inv=Inv HandshakeWithTypes.tla | sed 's/I@.*//'
...
The outcome is: ExecutionsTooShort
...
EXITCODE: OK
```

### check trivial violation of FALSE invariant (array-encoding)

```sh
$ apalache-mc check --length=2 --inv=Inv Bug20200306.tla | sed 's/I@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check Init without an assignment fails (array-encoding)

```sh
$ apalache-mc check --length=1 --inv=Inv Assignments20200309.tla
...
EXITCODE: ERROR (255)
[255]
```

### check Inline.tla suceeds (array-encoding)

```sh
$ apalache-mc check --length=5 Inline.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Rec1.tla succeeds typecheck

```sh
$ apalache-mc typecheck Rec1.tla | sed 's/I@.*//'
...
Type checker [OK]
...
EXITCODE: OK
```

### check Rec1.tla fails check

```sh
$ apalache-mc check --length=5 --inv=Inv Rec1.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (255)
```

### check Rec2.tla succeeds typecheck

```sh
$ apalache-mc typecheck Rec2.tla | sed 's/I@.*//'
...
Type checker [OK]
...
EXITCODE: OK
```

### check Rec2.tla fails check

```sh
$ apalache-mc check --length=5 --inv=Inv Rec2.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (255)
```

### check Rec3.tla succeeds typecheck

```sh
$ apalache-mc typecheck Rec3.tla | sed 's/I@.*//'
...
Type checker [OK]
...
EXITCODE: OK
```

### check Rec3.tla fails check
```sh
$ apalache-mc check --length=10 --inv=Inv Rec3.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (255)
```

### check Rec4.tla succeeds typecheck

```sh
$ apalache-mc typecheck Rec4.tla | sed 's/I@.*//'
...
Type checker [OK]
...
EXITCODE: OK
```

### check Rec4.tla fails check

Unfolding Fibonacci numbers

```sh
$ apalache-mc check --length=10 --inv=Inv Rec4.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (255)
```

### check Rec5.tla succeeds typecheck

```sh
$ apalache-mc typecheck Rec5.tla | sed 's/I@.*//'
...
Type checker [OK]
...
EXITCODE: OK
```

### check Rec5.tla fails check

```sh
$ apalache-mc check --length=5 --inv=Inv Rec5.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (255)
```

### check Rec6.tla succeeds typecheck

```sh
$ apalache-mc typecheck Rec6.tla | sed 's/I@.*//'
...
Type checker [OK]
...
EXITCODE: OK
```

### check Rec6.tla fails check

```sh
$ apalache-mc check --length=5 --inv=Inv Rec6.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (255)
```

### check Rec8.tla succeeds typecheck

```sh
$ apalache-mc typecheck Rec8.tla | sed 's/I@.*//'
...
Type checker [OK]
...
EXITCODE: OK
```

### check Rec8.tla fails check

```sh
$ apalache-mc check --length=10 --inv=Inv Rec8.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (255)
```

### check Rec9.tla succeeds typecheck

```sh
$ apalache-mc typecheck Rec9.tla | sed 's/I@.*//'
...
Type checker [OK]
...
EXITCODE: OK
```

### check Rec9.tla fails check

```sh
$ apalache-mc check --length=3 --inv=Inv Rec9.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (255)
```

### check Rec10.tla succeeds typecheck

```sh
$ apalache-mc typecheck Rec10.tla | sed 's/I@.*//'
...
Type checker [OK]
...
EXITCODE: OK
```

### check Rec10.tla fails check

```sh
$ apalache-mc check Rec10.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (255)
```

### check Rec11.tla succeeds typecheck

```sh
$ apalache-mc typecheck Rec11.tla | sed 's/I@.*//'
...
Type checker [OK]
...
EXITCODE: OK
```

### check Rec11.tla fails check

```sh
$ apalache-mc check Rec11.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (255)
```

### check Rec12.tla succeeds typecheck

```sh
$ apalache-mc typecheck Rec12.tla | sed 's/I@.*//'
...
Type checker [OK]
...
EXITCODE: OK
```

### check Rec12.tla fails check

```sh
$ apalache-mc check --inv=Inv Rec12.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (255)
```

### check Rec13.tla succeeds

```sh
$ apalache-mc check --inv=Inv Rec13.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check ExistsAsValue.tla succeeds

```sh
$ apalache-mc check --inv=Inv ExistsAsValue.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check reorderTest.tla MayFail succeeds: fixed SMT fails under SMT-based assignment finding

```sh
$ apalache-mc check --next=MayFail --tuning-options-file=reorderTest.properties reorderTest.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check reorderTest.tla MustFail fails

```sh
$ apalache-mc check --next=MustFail reorderTest.tla
...
EXITCODE: ERROR (255)
[255]
```

### check Empty.tla fails (array-encoding)

```sh
$ apalache-mc check Empty.tla
...
EXITCODE: ERROR (255)
[255]
```

### check NoVars.tla succeeds (array-encoding)

```sh
$ apalache-mc check --inv=Inv --length=1 NoVars.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check HourClock.tla without Init fails (array-encoding)

```sh
$ apalache-mc check --init=NonExistantInit HourClock.tla
...
EXITCODE: ERROR (255)
[255]
```

### check HourClock.tla without Next fails (array-encoding)

```sh
$ apalache-mc check --next=NonExistantNext HourClock.tla
...
EXITCODE: ERROR (255)
[255]
```

### check HourClock.tla without Inv fails (array-encoding)

```sh
$ apalache-mc check --inv=NonExistantInv HourClock.tla
...
EXITCODE: ERROR (255)
[255]
```

### check NonNullaryLet succeeds: regression for issue 429 (array-encoding)

```sh
$ apalache-mc check NonNullaryLet.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check CaseNoOther succeeds (array-encoding)

```sh
$ apalache-mc check CaseNoOther.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check CaseNoOtherBool succeeds (array-encoding)

```sh
$ apalache-mc check CaseNoOtherBool.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Callback.tla succeeds (array-encoding)

`Callback.tla` demonstrates that one can implement non-determinism with the existential operator and use a callback to
do an assignment to a variable. As it requires tricky operator inlining, here is the test.

```sh
$ apalache-mc check Callback.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check SimpT1 succeeds (array-encoding)

This test was moved from a unit test of SymbTransGenerator. The goal of the test is to check that symbolic transitions
are extracted from the spec. Hence, we run model checking only against the initial states.

```sh
$ apalache-mc check --length=0 SimpT1.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Selections succeeds (array-encoding)

```sh
$ apalache-mc check Selections.tla | sed 's/I@.*//'
...
Selections.tla:16:18-16:27: Missing assignments to: z
...
EXITCODE: ERROR (255)
```

### check test1 succeeds (array-encoding)

```sh
$ apalache-mc check test1.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check ITE_CASE succeeds (array-encoding)

```sh
$ apalache-mc check ITE_CASE.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (255)
```

### check Deadlock712 succeeds (array-encoding)

This test shows that Apalache may miss a deadlock, as discussed in issue 712.
Once this is fixed, Apalache should find a deadlock.

```sh
$ apalache-mc check Deadlock712.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check SimpleLambda succeeds
Regression test for https://github.com/informalsystems/apalache/issues/1446

```sh
$ apalache-mc check --inv=Inv SimpleLambda.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### check NestedCallByName succeeds
Regression test for embedding recursion

```sh
$ apalache-mc check --inv=Inv NestedCallByName.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### typecheck Bug914 fails

Regression test for https://github.com/informalsystems/apalache/issues/914 In
the earlier version, we expected the model checker to complain about
mismatching record types. The new type checker with row typing is reporting a
type error, and this is what we expect.

```sh
$ apalache-mc typecheck --features=rows Bug914.tla | sed 's/[IE]@.*//'
...
[Bug914.tla:21:9-21:26]: Arguments to = should have the same type. For arguments m, ["foo" ↦ TRUE] with types {  }, { foo: Bool }, in expression m = (["foo" ↦ TRUE])
[Bug914.tla:21:1-21:26]: Error when computing the type of Init
...
EXITCODE: ERROR (120)
```

### check RecordExcept987 succeeds

Regression test for https://github.com/informalsystems/apalache/issues/987
We should always use sorted keys on record types.

```sh
$ apalache-mc check --features=rows RecordExcept987.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### check Bug985 succeeds

Regression test for https://github.com/informalsystems/apalache/issues/985
Skolemization should be sound.

```sh
$ apalache-mc check Bug985.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### check Bug1126 succeeds

Regression test for https://github.com/informalsystems/apalache/issues/1126
An occurence of `Seq(S)` should point to an explanation.

```sh
$ apalache-mc check Bug1126.tla | sed 's/[IE]@.*//'
...
Bug1126.tla:15:14-15:27: unsupported expression: Seq(_) produces an infinite set of unbounded sequences. See: https://apalache.informal.systems/docs/apalache/known-issues.html#using-seqs
...
EXITCODE: ERROR (75)
```

### check SetSndRcv succeeds (array-encoding)

Regression test for https://github.com/informalsystems/apalache/issues/1152
Sets should not become unconstrained when choosing an element in a set minus operation.

```sh
$ apalache-mc check --inv=Inv --length=6 --cinit=CInit SetSndRcv.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### check SetAddDel succeeds (array-encoding)

Regression test for https://github.com/informalsystems/apalache/issues/1162
Sets should not become unconstrained when union is performed.

```sh
$ apalache-mc check --inv=Inv --length=6 --cinit=CInit SetAddDel.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### check PizzaOrder succeeds (array-encoding)

```sh
$ apalache-mc check --features=rows --cinit=ConstInit --inv=NoDoubleDelivery PizzaOrder.tla | sed 's/I@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check OracleFunSet succeeds (array-encoding)

Regression test for https://github.com/informalsystems/apalache/issues/1680
Function sets themselves should be able to be set elements.

```sh
$ apalache-mc check OracleFunSet.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### check Verifier_functionComparison fails (array-encoding)

Regression test for https://github.com/informalsystems/apalache/issues/1811
Comparisons with functions with empty domains should be sound (as should everything else)

```sh
$ apalache-mc check Verifier_functionComparison.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (12)
```

### check PickPerf succeeds (array-encoding)

A performance test.

```sh
$ apalache-mc check --discard-disabled=0 --tuning-options=search.invariant.mode=after PickPerf.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### check PickPerf2 succeeds (array-encoding)

A performance test.

```sh
$ apalache-mc check --discard-disabled=0 --tuning-options=search.invariant.mode=after PickPerf2.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### simulate y2k with --save-runs succeeds

```sh
$ apalache-mc simulate --length=10 --max-run=5 --save-runs --inv=Safety y2k_instance.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

## configure the check command

Testing various flags that are set via command-line options and the TLC configuration file. The CLI has priority over
the TLC config. So we have to test that it all works together.

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
EXITCODE: OK
```

### configure an invariant via CLI

```sh
$ apalache-mc check --inv=Inv Config.tla | sed 's/I@.*//'
...
  > Set an invariant to Inv
...
The outcome is: NoError
...
EXITCODE: OK
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
EXITCODE: ERROR (12)
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
Config.tla:58:5-58:14: unsupported expression: ♢(x > 10)
...
EXITCODE: ERROR (75)
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
Config.tla:58:5-58:14: unsupported expression: ♢(x > 10)
...
EXITCODE: ERROR (75)
```

### configure missing property in TLC config

```sh
$ apalache-mc check --config=Config3.cfg Config.tla | sed 's/[IE]@.*//'
...
  > Config3.cfg: Loading TLC configuration
...
Configuration error (see the manual): Operator NoLiveness not found (used as a temporal property)
...
EXITCODE: ERROR (255)
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
EXITCODE: OK
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
EXITCODE: OK
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
EXITCODE: OK
```

### configure complains about circular dependencies

```sh
$ apalache-mc check ConfigUnsorted.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (255)
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
...
The outcome is: NoError
...
EXITCODE: OK
```

### configure via TLC config and replace operators

The replacements make the invariant hold true.

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
EXITCODE: OK
```

### configure via TLC config on non-existant config

When a configuration file does not exist, the tool should error.

```sh
$ apalache-mc check --inv=Inv --config=ThisConfigDoesNotExist.cfg ConfigReplacements.tla | sed 's/[IEW]@.*//'
...
Configuration error (see the manual): TLC config file not found: ThisConfigDoesNotExist.cfg
...
EXITCODE: ERROR (255)
```

### configure via TLC config on no config

When a configuration file is not specified, the invariant should fail.

```sh
$ apalache-mc check --inv=Inv ConfigReplacements.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

## testing the slicer of symbolic transitions in TransitionFinderPass

### check Slicer1

```sh
$ apalache-mc check --inv=Inv Slicer1.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check Slicer2

```sh
$ apalache-mc check --inv=Inv Slicer2.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check Slicer3

```sh
$ apalache-mc check --inv=Inv Slicer3.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check Slicer4

```sh
$ apalache-mc check --inv=Inv Slicer4.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check Slicer5

```sh
$ apalache-mc check --inv=Inv Slicer5.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check ActionInv

```sh
$ apalache-mc check --inv=IncreaseInv ActionInv.tla | sed 's/[IEW]@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check ActionInv with a false invariant

```sh
$ apalache-mc check --inv=KeepInv ActionInv.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check Invariants with StateInv

```sh
$ apalache-mc check --inv=StateInv Invariants.tla | sed 's/[IEW]@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Invariants with BuggyStateInv

```sh
$ apalache-mc check --inv=BuggyStateInv Invariants.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check Invariants with ActionInv

```sh
$ apalache-mc check --inv=ActionInv Invariants.tla | sed 's/[IEW]@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Invariants with BuggyActionInv

```sh
$ apalache-mc check --inv=BuggyActionInv Invariants.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check Invariants with TraceInv

```sh
$ apalache-mc check --inv=TraceInv Invariants.tla | sed 's/[IEW]@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Invariants with BuggyTraceInv

```sh
$ apalache-mc check --inv=BuggyTraceInv Invariants.tla | sed 's/[IEW]@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check View.tla

```sh
$ apalache-mc check --inv=Inv --max-error=50 --view=View1 View.tla | sed 's/[IEW]@.*//'
...
Found 37 error(s)
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check View2.tla

```sh
$ apalache-mc check --inv=Inv --max-error=50 --view=View1 View2.tla | sed 's/[IEW]@.*//'
...
Found 20 error(s)
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check bug #874

Unhandled `IllegalArgumentException` when accessing a non-existent field on a
record. With the old records, this spec was failing during model checking.
With the new records, this spec is failing at type checking.

See https://github.com/informalsystems/apalache/issues/874

```sh
$ apalache-mc typecheck --features=rows Bug874.tla | sed 's/[IEW]@.*//'
...
[Bug874.tla:4:17-4:27]: Cannot apply ["a" ↦ 2] to the argument "b" in (["a" ↦ 2])["b"].
...
EXITCODE: ERROR (120)
```

### check letpoly.tla

Test that the model checker supports let-polymorphism.

```sh
$ apalache-mc check letpoly.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check letpoly_inst.tla

Test that the model checker supports let-polymorphism.

```sh
$ apalache-mc check letpoly_inst.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Bug1023.tla

Test that `--cinit` propagates constraints.

```sh
$ apalache-mc check --cinit=ConstInit --inv=Inv Bug1023.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Bug880.tla

Test that `ASSUME` propagates constraints.

```sh
$ apalache-mc check --cinit=ConstInit --inv=Inv Bug880.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Bug931.tla

Test that the model checker nicely complains about unresolved polymorphism.

```sh
$ apalache-mc check --inv=Inv Bug931.tla | sed 's/[IEW]@.*//'
...
Bug931.tla:6:20-6:21: type input error: Found a polymorphic type: Set(b)
...
EXITCODE: ERROR (255)
```

### check Bug1682.tla

```sh
$ apalache-mc check --init=Inv --inv=Inv --length=1 Bug1682.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Bug1735.tla (array-encoding)

```sh
$ apalache-mc check --inv=Inv --length=1 Bug1735.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (12)
```

### check Bug1794.tla

```sh
$ apalache-mc check --length=1 Bug1794.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check profiling

Check that the profiler output is produced as explained in
[Profiling](https://apalache.informal.systems/docs/apalache/profiling.html).

```sh
$ apalache-mc check --run-dir=./profile-run-dir --smtprof schroedinger_cat.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ head -n 1 ./profile-run-dir/profile.csv
# weight,nCells,nConsts,nSmtExprs,location
$ rm -rf ./profile-run-dir
```

### check ModelVal.tla succeeds

Test that model values are handled correctly.

```sh
$ apalache-mc check --cinit=CInit --inv=Inv ModelVal.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check ModelValFail.tla fails

Test that model values of different sorts are incomparable

```sh
$ apalache-mc check --cinit=CInit --inv=Inv ModelValFail.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (120)
```

### check MC3_TwoPhaseUFO.tla succeeds with model values

Test that advanced use of model values is working.

```sh
$ apalache-mc check --inv=TCConsistent MC3_TwoPhaseUFO.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check PolyFold.tla reports no error: regression for #1085

```sh
$ apalache-mc check --inv=Inv --length=1 PolyFold.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Test669.tla reports an error

```sh
$ apalache-mc check Test669.tla | sed 's/[IEW]@.*//'
...
This error may show up when CONSTANTS are not initialized.
Check the manual: https://apalache.informal.systems/docs/apalache/parameters.html
Input error (see the manual): SubstRule: Variable N is not assigned a value
...
EXITCODE: ERROR (255)
```

### check Bug1136.tla reports no error: regression for #1136

```sh
$ apalache-mc check --inv=Inv Bug1136.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Test928.tla reports no error on NoFail: regression for #928

```sh
$ apalache-mc check --inv=NoFail --length=1 Test928.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Test928.tla reports an error on Fail: regression for #928

```sh
$ apalache-mc check --inv=Fail --length=1 Test928.tla | sed 's/[IEW]@.*//'
...
Found a polymorphic type: Set(a)
Probable causes: an empty set { } needs a type annotation or an incorrect record field is used
Test928.tla:20:23-20:24: type input error: Found a polymorphic type: Set(a)
...
EXITCODE: ERROR (255)
```

### check Test1182.tla reports no error on Inv: regression for #1182

```sh
$ apalache-mc check --inv=Inv Test1182.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Test951.tla reports no error on Inv: regression for #951

```sh
$ apalache-mc check --inv=Inv Test951.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Test1259.tla reports no error: regression for #1259

```sh
$ apalache-mc check Test1259.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Test1226.tla reports no error

```sh
$ apalache-mc check --length=1 --inv=Inv Test1226.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check MegaSpec1.tla reports no error with `--debug`: regression for #1313

```sh
$ apalache-mc check --debug --cinit=CInit MegaSpec1.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Test1305.tla reports 10 errors

Regression test for #1305.

```sh
$ apalache-mc check --inv=Inv --view=View  --max-error=10 Test1305.tla | sed 's/[IEW]@.*//'
...
Found 10 error(s)
...
EXITCODE: ERROR (12)
```

### check TestSequences.tla reports no error

```sh
$ apalache-mc check --length=0 --inv=AllTests TestSequences.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestSequencesExt.tla reports no error

```sh
$ apalache-mc check --length=0 --inv=AllTests TestSequencesExt.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestBags.tla reports no error

```sh
$ apalache-mc check --length=0 --inv=Inv TestBags.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestBagsExt.tla reports no error

```sh
$ apalache-mc check --length=0 --inv=AllTests TestBagsExt.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestInlining.tla reports no error

```sh
$ apalache-mc check --length=0 --inv=AllTests TestInlining.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestFolds.tla reports an error

```sh
$ apalache-mc check --length=0 --inv=AllTests TestFolds.tla | sed 's/[IEW]@.*//'
...
TestFolds.tla:21:5-21:50: unsupported expression: Not supported: MapThenFoldSet. Use FoldSet, FoldSeq, FoldFunction.
...
EXITCODE: ERROR (75)
```

### check Test1343.tla reports no error

Regression test for #1343

```sh
$ apalache-mc check --length=2 Test1343.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestSets.tla reports no error (array-encoding)

```sh
$ apalache-mc check --length=0 --inv=AllTests TestSets.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestCommunityFunctions.tla reports no error (array-encoding)

```sh
$ apalache-mc check --length=0 --inv=AllTests TestCommunityFunctions.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestFiniteSetsExt.tla reports no error (array-encoding)

```sh
$ apalache-mc check --length=0 --inv=AllTests TestFiniteSetsExt.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestFunctions.tla reports no error

```sh
$ apalache-mc check --length=0 --inv=AllTests TestFunctions.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestBuiltinAsArg1626.tla reports no error (array-encoding)

```sh
$ apalache-mc check --length=0 --inv=AllTests TestBuiltinAsArg1626.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestHash2.tla reports no error (array-encoding)

A regression test for using `--cinit` and hashes.

```sh
$ apalache-mc check --inv=Inv --cinit=ConstInit TestHash2.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Test1425.tla reports no error

A regression test for assignments under quantification over empty sets.

```sh
$ apalache-mc check --length=1 Test1425.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Test1623.tla reports no error

A regression test for #1623 (Instantiation with .cfg + ASSUME)

```sh
$ apalache-mc check --length=3 --config=Test1623.cfg --inv=Inv Test1623.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check MC_FoldExcept3.tla (slow) reports no error

A test for folds with excepts, the slow case.

```sh
$ apalache-mc check --inv=DriftInv --next=NextSlow antipatterns/fold-except/MC_FoldExcept3.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check MC_FoldExcept3.tla (fast) reports no error

A test for folds with excepts, the fast case.

```sh
$ apalache-mc check --inv=DriftInv --next=NextFast antipatterns/fold-except/MC_FoldExcept3.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check RecMem1627.tla reports no error

A test for folds with excepts, the fast case.

```sh
$ apalache-mc check --features=rows --inv=TypeOK --length=1 RecMem1627.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check UnchangedAsInv1663.tla reports no error

A test `UNCHANGED` in an invariant.

```sh
$ apalache-mc check --inv=Inv --length=1 UnchangedAsInv1663.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestRecordsNew.tla

Check row-based records support row typing.

```sh
$ apalache-mc check --features=rows TestRecordsNew.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check MC_LamportMutexTyped.tla

Check the mutex algorithm with new records.

```sh
$ apalache-mc check --features=rows --length=4 MC_LamportMutexTyped.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

## running the typecheck command

### typecheck Empty.tla reports no error

```sh
$ apalache-mc typecheck Empty.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### typecheck Empty.tla reports no error when rows enabled

```sh
$ apalache-mc typecheck --features=rows Empty.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### typecheck ExistTuple476.tla reports no error: regression for issues 476 and 482

```sh
$ apalache-mc typecheck ExistTuple476.tla | sed 's/I@.*//'
...
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck CarTalkPuzzleTyped.tla

```sh
$ apalache-mc typecheck CarTalkPuzzleTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
 > All expressions are typed
Type checker [OK]
...
EXITCODE: OK
```

### typecheck CigaretteSmokersTyped.tla

```sh
$ apalache-mc typecheck --features=rows CigaretteSmokersTyped.tla | sed 's/[IEW]@.*//'
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
 > Your types are purrfect!
 > All expressions are typed
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
 > Your types are purrfect!
 > All expressions are typed
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
 > Your types are purrfect!
 > All expressions are typed
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
 > Your types are purrfect!
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
 > Your types are purrfect!
 > All expressions are typed
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
 > Your types are purrfect!
 > All expressions are typed
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
 > Your types are purrfect!
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
 > Your types are purrfect!
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
 > Your types are purrfect!
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
EXITCODE: ERROR (255)
```

### typecheck ChannelTyped.tla

```sh
$ apalache-mc typecheck ChannelTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
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
 > Your types are purrfect!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck ChangRobertsTyped.tla

```sh
$ apalache-mc typecheck ChangRobertsTyped.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck ChangRobertsTyped_Test.tla

```sh
$ apalache-mc typecheck ChangRobertsTyped_Test.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
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
 > Your types are purrfect!
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
 > Your types are purrfect!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck Except617.tla

```sh
$ apalache-mc typecheck --features=rows Except617.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
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
 > Your types are purrfect!
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
EXITCODE: ERROR (255)
```

### typecheck UntypedVar.tla

```sh
$ apalache-mc typecheck UntypedVar.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
Typing input error: Expected a type annotation for VARIABLE x
...
EXITCODE: ERROR (255)
```

### typecheck TestAnnotations.tla

```sh
$ apalache-mc typecheck TestAnnotations.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck schroedinger_cat.tla

```sh
$ apalache-mc typecheck schroedinger_cat.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck bug #860

Unhandled exception thrown when type-checking a spec that uses the wrong
annotation syntax for operators.

See https://github.com/informalsystems/apalache/issues/860

```sh
$ apalache-mc typecheck Bug860.tla | sed 's/[IEW]@.*//'
...
Parsing error in the type annotation:  (Int, Int) -> Bool
Typing input error: Parser error in type annotation of Op: '=>' expected but -> found
...
EXITCODE: ERROR (255)
```

### typecheck bug #832

Unhandled exception thrown due to incorrect annotation of a tuple return
type.

See https://github.com/informalsystems/apalache/issues/832

```sh
$ apalache-mc typecheck Bug832.tla | sed 's/[IEW]@.*//'
...
Parsing error in the type annotation:  () => (Bool, Bool)
Typing input error: Parser error in type annotation of Example: '->' expected but ) found
...
EXITCODE: ERROR (255)
```

### typecheck bug #925

Type unification should not recurse infinitely.

See: https://github.com/informalsystems/apalache/issues/925

```sh
$ apalache-mc typecheck --features=rows Bug925.tla | sed 's/[IEW]@.*//'
...
[Bug925.tla:7:1-7:24]: Error when computing the type of Optional
...
EXITCODE: ERROR (120)
```

### typecheck letpoly.tla

Test the Snowcat support let-polymorphism.

```sh
$ apalache-mc typecheck letpoly.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck letpoly_inst.tla

Test the Snowcat support let-polymorphism.

```sh
$ apalache-mc typecheck letpoly_inst.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck Poly1084.tla

Regression test for principal types in let definitions.

```sh
$ apalache-mc typecheck Poly1084.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck Poly1085.tla

Regression test for principal types in let definitions.

```sh
$ apalache-mc typecheck Poly1085.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck Poly1088.tla

Regression test for principal types in let definitions.

```sh
$ apalache-mc typecheck Poly1085.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck Poly1107.tla

Regression test for principal types in let definitions.

```sh
$ apalache-mc typecheck Poly1107.tla | sed 's/[IEW]@.*//'
...
PASS #1: TypeCheckerSnowcat
 > Running Snowcat .::.
 > Your types are purrfect!
 > All expressions are typed
...
Type checker [OK]
...
EXITCODE: OK
```

### typecheck LamportMutexTyped.tla

Typecheck a real spec by Leslie Lamport.

```sh
$ apalache-mc typecheck --features=rows LamportMutexTyped.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### typecheck MC_LamportMutexTyped.tla

Typecheck a model checking instance.

```sh
$ apalache-mc typecheck --features=rows MC_LamportMutexTyped.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### typecheck TestFolds.tla

Typecheck the test for Folds.tla.

```sh
$ apalache-mc typecheck TestFolds.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### typecheck TestRecordsNew.tla

Typecheck new records that support row typing.

```sh
$ apalache-mc typecheck --features=rows TestRecordsNew.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### typecheck TestRecordsNewIll1.tla

No ill-typed record access.

```sh
$ apalache-mc typecheck --features=rows TestRecordsNewIll1.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (120)
```

### typecheck TestRecordsNewIll2.tla

No ill-typed record access.

```sh
$ apalache-mc typecheck --features=rows TestRecordsNewIll2.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (120)
```

### typecheck TestRecordsNewIll3.tla

No ill-typed record access.

```sh
$ apalache-mc typecheck --features=rows TestRecordsNewIll3.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (120)
```

### typecheck TestRecordsNewIll4.tla

No ill-typed record access.

```sh
$ apalache-mc typecheck --features=rows TestRecordsNewIll4.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (120)
```

### typecheck TestVariants.tla

Variant operators are type correct.

```sh
$ apalache-mc typecheck --features=rows TestVariants.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### typecheck TestReqAckVariants.tla

```sh
$ apalache-mc typecheck --features=rows TestReqAckVariants.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

## configuring the output manager

### output manager: set out-dir by CLI flag
If we run with the `--out-dir` flag

```sh
$ apalache-mc check --out-dir=./test-out-dir --write-intermediate=0 --length=0 Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

```sh
$ find ./test-out-dir/Counter.tla/* -type f -exec basename {} \; | ./sort.sh
detailed.log
example0.itf.json
example0.json
example0.tla
example.itf.json
example.json
example.tla
log0.smt
MCexample0.out
MCexample.out
run.txt
```

Be sure to clean up

```sh
$ rm -rf ./test-out-dir
```

### output manager: set out-dir by envvar

```sh
$ OUT_DIR=./test-out-dir apalache-mc check --length=0 Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ test -d test-out-dir
$ rm -rf ./test-out-dir
```

### output manager: setting out-dir by CLI flag overrides the envvar

```sh
$ OUT_DIR=./not-here apalache-mc check --out-dir=./test-out-dir --length=0 Counter.tla
...
EXITCODE: OK
$ test -d test-out-dir
$ !(test -d not-here)
$ rm -rf ./test-out-dir
```

### output manager: write-intermediate files

```sh
$ apalache-mc check --out-dir=./test-out-dir --write-intermediate=true --length=0 Counter.tla | sed 's/[IEW]@.*//' 
...
EXITCODE: OK
$ find ./test-out-dir/Counter.tla/* -type f -exec basename {} \; | ./sort.sh
00_OutSanyParser.json
00_OutSanyParser.tla
01_OutTypeCheckerSnowcat.json
01_OutTypeCheckerSnowcat.tla
02_OutConfigurationPass.json
02_OutConfigurationPass.tla
03_OutDesugarerPass.json
03_OutDesugarerPass.tla
04_OutInlinePass.json
04_OutInlinePass.tla
05_OutPrimingPass.json
05_OutPrimingPass.tla
06_OutVCGen.json
06_OutVCGen.tla
07_OutPreprocessingPass.json
07_OutPreprocessingPass.tla
08_OutTransitionFinderPass.json
08_OutTransitionFinderPass.tla
09_OutOptimizationPass.json
09_OutOptimizationPass.tla
10_OutAnalysisPass.json
10_OutAnalysisPass.tla
11_OutPostTypeCheckerSnowcat.json
11_OutPostTypeCheckerSnowcat.tla
detailed.log
example0.itf.json
example0.json
example0.tla
example.itf.json
example.json
example.tla
log0.smt
MCexample0.out
MCexample.out
run.txt
$ rm -rf ./test-out-dir
```

### output manager: use the --profiling flag to write profile-rules.txt

```sh
$ apalache-mc check --out-dir=./test-out-dir --profiling=true --length=0 Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ test -s ./test-out-dir/Counter.tla/*/profile-rules.txt
$ rm -rf ./test-out-dir
```

### output manager: counterexamples are written to the run directory

```sh
$ apalache-mc check --out-dir=./test-out-dir --write-intermediate=0 --length=2 --inv=Inv factorization.tla | sed -e 's/[IEW]@.*//'
...
EXITCODE: ERROR (12)
$ ls ./test-out-dir/factorization.tla/* | ./sort.sh
detailed.log
log0.smt
MCviolation1.out
MCviolation.out
run.txt
violation1.itf.json
violation1.json
violation1.tla
violation.itf.json
violation.json
violation.tla
$ rm -rf ./test-out-dir
```

### output manager: intermediate output can be written to specified run directory

```sh
$ apalache-mc check --out-dir=./test-out-dir --run-dir=./test-run-dir --write-intermediate=true --length=0 Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ find ./test-run-dir -type f -exec basename {} \; | ./sort.sh
00_OutSanyParser.json
00_OutSanyParser.tla
01_OutTypeCheckerSnowcat.json
01_OutTypeCheckerSnowcat.tla
02_OutConfigurationPass.json
02_OutConfigurationPass.tla
03_OutDesugarerPass.json
03_OutDesugarerPass.tla
04_OutInlinePass.json
04_OutInlinePass.tla
05_OutPrimingPass.json
05_OutPrimingPass.tla
06_OutVCGen.json
06_OutVCGen.tla
07_OutPreprocessingPass.json
07_OutPreprocessingPass.tla
08_OutTransitionFinderPass.json
08_OutTransitionFinderPass.tla
09_OutOptimizationPass.json
09_OutOptimizationPass.tla
10_OutAnalysisPass.json
10_OutAnalysisPass.tla
11_OutPostTypeCheckerSnowcat.json
11_OutPostTypeCheckerSnowcat.tla
detailed.log
example0.itf.json
example0.json
example0.tla
example.itf.json
example.json
example.tla
MCexample0.out
MCexample.out
run.txt
$ rm -rf ./test-out-dir ./test-run-dir
```

### output manager: counterexamples can be written to specified run directory

```sh
$ apalache-mc check --out-dir=./test-out-dir --write-intermediate=0 --length=2 --inv=Inv --run-dir=./test-run-dir factorization.tla | sed -e 's/[IEW]@.*//'
...
EXITCODE: ERROR (12)
$ ls ./test-run-dir | ./sort.sh
detailed.log
MCviolation1.out
MCviolation.out
run.txt
violation1.itf.json
violation1.json
violation1.tla
violation.itf.json
violation.json
violation.tla
$ rm -rf ./test-out-dir ./test-run-dir
```

## configuration management

### configuration management: read run-dir from local `.apalache.cfg`

```sh
$ echo "run-dir: ./configured-run-dir" > .apalache.cfg
$ apalache-mc check --length=0 Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ ls ./configured-run-dir | ./sort.sh
detailed.log
example0.itf.json
example0.json
example0.tla
example.itf.json
example.json
example.tla
MCexample0.out
MCexample.out
run.txt
$ rm -rf ./configured-run-dir ./.apalache.cfg
```

### configuration management: CLI config file overrides local `.apalache.cfg`

```sh
$ echo "run-dir: ./to-override-dir" > .apalache.cfg
$ echo "run-dir: ./configured-run-dir" > cli-config.cfg
$ apalache-mc check --config-file=cli-config.cfg --length=0 Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ ! test -d ./to-override-dir
$ test -d ./configured-run-dir
$ rm -rf ./configured-run-dir ./.apalache.cfg ./cli-config.cfg
```

### configuration management: CLI argument overrides config-file

```sh
$ echo "run-dir: ./to-override-dir" > cli-config.cfg
$ apalache-mc check --config-file=cli-config.cfg --run-dir=./configured-run-dir --length=0 Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ ! test -d ./to-override-dir
$ test -d ./configured-run-dir
$ rm -rf ./configured-run-dir ./cli-config.cfg
```

### configuration management: tilde is expanded in configured paths

We set `user.home` to the current working directly, so we can test tilde
expansion in the path without writing outside of the test directory.

NOTE: We need to set the home to a relative path to the cwd in order to
ensure the tests also works in the docker container.

```sh
$ echo "run-dir: ~/run-dir" > .apalache.cfg
$ JVM_ARGS="-Duser.home=." apalache-mc check --length=0 Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ test -d ./run-dir
$ rm -rf ./run-dir ./.apalache.cfg
```

### configuration management: invalid features are rejected with error

```sh
$ echo "features: [ invalid-feature ]" > .apalache.cfg
$ apalache-mc check --length=0 Counter.tla | grep -o -e "Configuration error: at 'features.0'" -e "Cannot convert 'invalid-feature' to at.forsyte.apalache.tla.lir.Feature"
...
Configuration error: at 'features.0'
Cannot convert 'invalid-feature' to at.forsyte.apalache.tla.lir.Feature
$ rm -rf ./.apalache.cfg
```

## module lookup

### module lookup: looks up dummy module from standard library

```sh
$ cd module-lookup/subdir-no-dummy && apalache-mc parse --output=output.tla Including.tla
...
EXITCODE: OK
$ cat module-lookup/subdir-no-dummy/output.tla
-------------------------------- MODULE output --------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

Init == TRUE

Next == TRUE

================================================================================
$ rm module-lookup/subdir-no-dummy/output.tla
```

### module lookup: looks up modules in the same directory

Regression test for https://github.com/informalsystems/apalache/issues/426

Look up files in the same directory as the file supplied on commandline.

Files in that directory take precedence over the Apalache standard library.

```sh
$ apalache-mc parse --output=output.tla module-lookup/subdir/Including.tla
...
EXITCODE: OK
$ cat output.tla | grep VARIABLE
VARIABLE same_dir
$ rm output.tla
```

### module lookup: looks up modules in the current working directory

Files in current working directory take precedence over

- files in the same directory as the supplied file
- the Apalache standard library

```sh
$ cd module-lookup && apalache-mc parse --output=output.tla subdir/Including.tla
...
EXITCODE: OK
$ cat module-lookup/output.tla | grep VARIABLE
VARIABLE parent_dir
$ rm module-lookup/output.tla
```

### module lookup: looks up modules when in same directory

Test relative paths without prefixed directories

```sh
$ cd module-lookup/subdir && apalache-mc parse --output=output.tla Including.tla
...
EXITCODE: OK
$ cat module-lookup/subdir/output.tla | grep VARIABLE
VARIABLE same_dir
$ rm module-lookup/subdir/output.tla
```

## server mode

### server mode: server can be started

We start the server, save its process id, then wait long enough for it to spin
up and output its welcome message, before killing it:

```sh
$ apalache-mc server & pid=$! && sleep 3 && kill $pid
...
The Apalache server is running. Press Ctrl-C to stop.
```
