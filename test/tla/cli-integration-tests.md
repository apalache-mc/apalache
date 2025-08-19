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

## error handling for invalid file formats

Ensure we give a proper user error if invalid file format extension is given in
input. See https://github.com/apalache-mc/apalache/issues/2175 .

```sh
$ for cmd in check parse typecheck transpile; do apalache-mc $cmd f.badext 2>&1 | grep -o -e "EXITCODE: ERROR (255)" -e "Configuration error: Unsupported file format badext"; done
Configuration error: Unsupported file format badext
EXITCODE: ERROR (255)
Configuration error: Unsupported file format badext
EXITCODE: ERROR (255)
Configuration error: Unsupported file format badext
EXITCODE: ERROR (255)
Configuration error: Unsupported file format badext
EXITCODE: ERROR (255)
```

## running the parse command

This command parses a TLA+ specification with the SANY parser.

### parse blank file fails nicely

Create an empty file
```sh
$ touch blank.tla
```

Try to parse a blank file
```sh
$ apalache-mc parse blank.tla | sed 's/E@.*//'
...
Parsing error: No root module defined in file
...
EXITCODE: ERROR (255)
```

Cleanup
```sh
$ rm blank.tla
```

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

### parse Empty with --features=no-rows succeeds

```sh
$ apalache-mc parse --features=no-rows Empty.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### parse Empty with an unsupported feature fails

```sh
$ apalache-mc parse --features=feature.unsupported Empty.tla 2>&1 | grep 'Failed to parse'
Failed to parse command parse: Incorrect value for option features, got 'feature.unsupported', expected a feature: rows, no-rows
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
[Test1275:5:1-5:12]: Syntax error in annotation -- ';' expected but end of source found
...
EXITCODE: OK
...
```

### parse Bug2429 succeeds

Long lines caused an issue with Apalache's source position handling (see #2429).

```sh
$ apalache-mc parse Bug2429.tla | sed 's/W@.*//'
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

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache, Variants

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
  "description": "https://apalache-mc.org/docs/adr/005adr-json.html",
  "modules": [
    {
      "kind": "TlaModule",
      "name": "output",
      "declarations": [
        {
$ rm output.json
```

### parse on an ITF file fails with an error

Check that we give an informative error if a user tries to invoke `parse` on a
`itf.json` file.

```sh
$ touch foo.itf.json
$ apalache-mc parse foo.itf.json | sed -e 's/I@.*//' -e 's/E@.*//'
...
Parsing error: Parsing the ITF format is not supported
...
EXITCODE: ERROR (255)
$ rm foo.itf.json
```

### parsing and emitting JSON IR

#### can check the spec from JSON produced by parsing the MegaSpec1.tla to JSON

A round-trip test for our JSON serialization and deserialization.

```sh
$ apalache-mc typecheck --output=megaspec1.json MegaSpec1.tla
...
EXITCODE: OK
$ apalache-mc check --length=0 --cinit=CInit megaspec1.json
...
EXITCODE: OK
$ rm megaspec1.json
```

### typecheck --output=output.tla Annotations succeeds

Check that it actually parses into TLA (see #1284)

```sh
$ apalache-mc typecheck --output=output.tla Annotations.tla | sed 's/I@.*//'
...
EXITCODE: OK
$ cat output.tla | head
-------------------------------- MODULE output --------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache, Variants

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
  "description": "https://apalache-mc.org/docs/adr/005adr-json.html",
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
$ apalache-mc test TestGen.tla Prepare Test Assertion | sed 's/I@.*//'
...
The outcome is: Error
Found a violation of the postcondition. Check violation.tla.
...
EXITCODE: ERROR (12)
```

## running the check command

### Prints default computation length of 10 (regression #2087)

```sh
$ apalache-mc check y2k_instance.tla | sed 's/I@.*//'
...
The outcome is: NoError
Checker reports no error up to computation length 10
...
EXITCODE: OK
```

### check factorization find a counterexample (array-encoding)

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
$ apalache-mc check --length=10 Fix365_ExistsSubset3.tla | sed 's/I@.*//'
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
$ apalache-mc check --cinit=CInit Bug540.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check Bug593 fails correctly: regression for issue 593 (array-encoding)

```sh
$ apalache-mc check Bug593.tla | sed 's/I@.*//'
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
$ apalache-mc check --cinit=AvoidBug --length=5 --inv=IsIndependent mis.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check mis.tla errors on IntroBug

```sh
$ apalache-mc check --cinit=IntroBug --length=5 --inv=IsIndependent mis.tla | sed 's/I@.*//'
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

### check Repeat succeeds

```sh
$ apalache-mc check --inv=Inv --length=0 Repeat.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check RepeatBad fails

```sh
$ apalache-mc check --inv=Inv --length=0 RepeatBad.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (255)
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
Checker reports no error up to computation length 19
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
$ apalache-mc check --length=4 --inv=Inv HandshakeWithTypes.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### check HandshakeWithTypes.tla with length 5 deadlocks (array-encoding)

```sh
$ apalache-mc check --length=5 --inv=Inv HandshakeWithTypes.tla | sed 's/I@.*//'
...
The outcome is: Deadlock
...
EXITCODE: ERROR (12)
```

### check HandshakeWithTypes.tla with length 5 passes with --no-deadlock

The option `--no-deadlock` forces the model checker to pass, even if it cannot
extend an execution prefix. See a discussion in
[#1640](https://github.com/apalache-mc/apalache/issues/1640).

```sh
$ apalache-mc check --length=5 --no-deadlock=1 --inv=Inv HandshakeWithTypes.tla | sed 's/I@.*//'
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
Regression test for https://github.com/apalache-mc/apalache/issues/1446

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

Regression test for https://github.com/apalache-mc/apalache/issues/914 In
the earlier version, we expected the model checker to complain about
mismatching record types. The new type checker with row typing is reporting a
type error, and this is what we expect.

```sh
$ apalache-mc typecheck Bug914.tla | sed 's/[IE]@.*//'
...
[Bug914.tla:21:9-21:26]: Arguments to = should have the same type. For arguments m, ["foo" ↦ TRUE] with types {  }, { foo: Bool }, in expression m = (["foo" ↦ TRUE])
[Bug914.tla:21:1-21:26]: Error when computing the type of Init
...
EXITCODE: ERROR (120)
```

### check RecordExcept987 succeeds

Regression test for https://github.com/apalache-mc/apalache/issues/987
We should always use sorted keys on record types.

```sh
$ apalache-mc check RecordExcept987.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### check Bug985 succeeds

Regression test for https://github.com/apalache-mc/apalache/issues/985
Skolemization should be sound.

```sh
$ apalache-mc check Bug985.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### check Bug1126 succeeds

Regression test for https://github.com/apalache-mc/apalache/issues/1126
An occurence of `Seq(S)` should point to an explanation.

```sh
$ apalache-mc check Bug1126.tla | sed 's/[IE]@.*//'
...
Bug1126.tla:15:14-15:27: unsupported expression: Seq(_) produces an infinite set of unbounded sequences. See: https://apalache-mc.org/docs/apalache/known-issues.html#using-seqs
...
EXITCODE: ERROR (75)
```

### check --inv with a temporal property fails (temporal)

```sh
$ apalache-mc check --inv=FalseLiveness LongPrefix.tla
...
EXITCODE: ERROR (255)
[255]
```

### check FalseLiveness fails (temporal)

```sh
$ apalache-mc check --temporal=FalseLiveness LongPrefix.tla
...
EXITCODE: ERROR (12)
[12]
```

### check Liveness succeeds (temporal)

```sh
$ apalache-mc check --temporal=Liveness LongPrefix.tla
...
EXITCODE: OK
```

### check LongLoops: Liveness succeeds (temporal)

```sh
$ apalache-mc check --temporal=Liveness LongLoops.tla
...
EXITCODE: OK
```

### check LongLoops: FalseLiveness fails (temporal)

```sh
$ apalache-mc check --temporal=FalseLiveness LongLoops.tla
...
EXITCODE: ERROR (12)
[12]
```

### check NoLoopsNoProblems succeeds (temporal)

```sh
$ apalache-mc check --temporal=Liveness NoLoopsNoProblems.tla
...
EXITCODE: OK
```

```sh
$ apalache-mc check --temporal=FalseLiveness NoLoopsNoProblems.tla
...
EXITCODE: OK
```

### check ManyBoxes (temporal)

```sh
$ apalache-mc check --temporal=Liveness ManyBoxes.tla
...
EXITCODE: OK
```

```sh
$ apalache-mc check --temporal=FalseLiveness ManyBoxes.tla
...
EXITCODE: ERROR (12)
[12]
```

### check ManyDiamonds (temporal)

```sh
$ apalache-mc check --temporal=Liveness ManyDiamonds.tla
...
EXITCODE: OK
```

```sh
$ apalache-mc check --temporal=FalseLiveness ManyDiamonds.tla
...
EXITCODE: ERROR (12)
[12]
```

### check DiamondBox (temporal)

```sh
$ apalache-mc check --temporal=Liveness DiamondBox.tla
...
EXITCODE: OK
```

```sh
$ apalache-mc check --temporal=FalseLiveness DiamondBox.tla
...
EXITCODE: ERROR (12)
[12]
```

### check BoxDiamond (temporal)

```sh
$ apalache-mc check --temporal=Liveness BoxDiamond.tla
...
EXITCODE: OK
```

```sh
$ apalache-mc check --temporal=FalseLiveness BoxDiamond.tla
...
EXITCODE: ERROR (12)
[12]
```

### check NestedTemporalInBool (temporal)

```sh
$ apalache-mc check --temporal=Liveness NestedTemporalInBool.tla
...
EXITCODE: OK
```

```sh
$ apalache-mc check --temporal=FalseLiveness NestedTemporalInBool.tla
...
EXITCODE: ERROR (12)
[12]
```

### check NoTemporalOperatorsInTemporalProp (temporal)

```sh
$ apalache-mc check --temporal=Property NoTemporalOperatorsInTemporalProp.tla
...
EXITCODE: OK
```

```sh
$ apalache-mc check --temporal=PropertyWithTemporal NoTemporalOperatorsInTemporalProp.tla
...
EXITCODE: OK
```

```sh
$ apalache-mc check --temporal=ExplicitInvariant NoTemporalOperatorsInTemporalProp.tla
...
EXITCODE: ERROR (12)
[12]
```

### check actions in temporal operators (temporal)

```sh
$ apalache-mc check --temporal=Liveness TemporalPropsOverActions.tla
...
EXITCODE: OK
```

```sh
$ apalache-mc check --temporal=FalseLiveness TemporalPropsOverActions.tla
...
EXITCODE: ERROR (12)
[12]
```

### check LetIn (temporal)

```sh
$ apalache-mc check --temporal=Liveness LetIn.tla
...
EXITCODE: OK
```

```sh
$ apalache-mc check --temporal=FalseLiveness LetIn.tla
...
EXITCODE: ERROR (12)
[12]
```

### check SetSndRcv succeeds (array-encoding)

Regression test for https://github.com/apalache-mc/apalache/issues/1152
Sets should not become unconstrained when choosing an element in a set minus operation.

```sh
$ apalache-mc check --inv=Inv --length=6 --cinit=CInit SetSndRcv.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### check SetAddDel succeeds (array-encoding)

Regression test for https://github.com/apalache-mc/apalache/issues/1162
Sets should not become unconstrained when union is performed.

```sh
$ apalache-mc check --inv=Inv --length=6 --cinit=CInit SetAddDel.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### check PizzaOrder succeeds (array-encoding)

```sh
$ apalache-mc check --cinit=ConstInit --inv=NoDoubleDelivery PizzaOrder.tla | sed 's/I@.*//'
...
The outcome is: Error
...
EXITCODE: ERROR (12)
```

### check OracleFunSet succeeds (array-encoding)

Regression test for https://github.com/apalache-mc/apalache/issues/1680
Function sets themselves should be able to be set elements.

```sh
$ apalache-mc check OracleFunSet.tla | sed 's/I@.*//'
...
EXITCODE: OK
```

### check Verifier_functionComparison fails (array-encoding)

Regression test for https://github.com/apalache-mc/apalache/issues/1811
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

### check TrivialFail fails with --discard-disabled=false

Regression test for https://github.com/apalache-mc/apalache/issues/2158

```sh
$ apalache-mc check --inv=Inv --discard-disabled=false TrivialFail.tla | sed 's/I@.*//'
...
EXITCODE: ERROR (12)
```

### check ConstantOperatorImpl succeeds

Test that model checking properly handles first-order `CONSTANTS`.

Regression test for https://github.com/apalache-mc/apalache/issues/2388

```sh
$ apalache-mc check --length=0 --inv=Inv ConstantOperatorImpl.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### simulate Paxos.tla with timeout succeeds

While we cannot rely on an actual timeout happening or not, we can make sure that the option is properly parsed. 

```sh
$ apalache-mc simulate --timeout-smt=1 --length=10 --inv=Inv Paxos.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

### simulate y2k with --output-traces succeeds

```sh
$ apalache-mc simulate --out-dir=./test-out-dir --length=10 --max-run=5 --output-traces --inv=Safety y2k_instance.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

```sh
$ find ./test-out-dir/y2k_instance.tla/* -type f -exec basename {} \; | ./sort.sh
detailed.log
example1.itf.json
example1.json
example1.tla
example2.itf.json
example2.json
example2.tla
example3.itf.json
example3.json
example3.tla
example4.itf.json
example4.json
example4.tla
example5.itf.json
example5.json
example5.tla
example.itf.json
example.json
example.tla
log0.smt
MCexample1.out
MCexample2.out
MCexample3.out
MCexample4.out
MCexample5.out
MCexample.out
run.txt
$ rm -rf ./test-out-dir
```

## configure the check command

Testing various flags that are set via command-line options and the TLC configuration file. The CLI has priority over
the TLC config. So we have to test that it all works together.

### configure default Init and Next

```sh
$ apalache-mc check Config.tla | sed 's/I@.*//'
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
  > Set the initialization predicate to Init1
  > Set the transition predicate to Next1
  > Set an invariant to Inv1
  > Set a temporal property to AwesomeLiveness
...
EXITCODE: OK
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
...
State 7: state invariant 0 violated.
Found 1 error(s)
The outcome is: Error
Checker has found an error
...
EXITCODE: ERROR (12)
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
  > Using init predicate(s) Init from the TLC config
  > Using next predicate(s) Next from the TLC config
  > Using inv predicate(s) Inv from the TLC config
...
  > ConfigParams.cfg: found INVARIANTS: Inv
  > Set the initialization predicate to Init
  > Set the transition predicate to Next
  > Set the constant initialization predicate to CInit
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
  > Using init predicate(s) Init from the TLC config
  > Using next predicate(s) Next from the TLC config
  > Using inv predicate(s) Inv from the TLC config
...
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

NOTE: We truncate the output to avoid printing the file name, making the test
indifferent to the execution environment (including in docker). This is required
since the error message includes an absolute file name, and this differs
depending on which computer it is running on.

```sh
$ apalache-mc check --inv=Inv --config=ThisConfigDoesNotExist.cfg ConfigReplacements.tla 2>&1 | grep -o -e "Specified TLC config file not found" -e "EXITCODE: ERROR (255)"
Specified TLC config file not found
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

### enable debug mode, which outputs SMT log

```sh
$ apalache-mc check --out-dir=./test-out-dir --length=0 --debug Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ find ./test-out-dir/Counter.tla/* -type f -exec basename {} \; | ./sort.sh
application-configs.cfg
detailed.log
log0.smt
run.txt
$ find ./test-out-dir/Counter.tla/* -type f -name log0.smt -exec cat {} \;
;; fp.spacer.random_seed = 0
;; nlsat.seed = 0
;; sat.random_seed = 0
;; sls.random_seed = 0
;; smt.random_seed = 0
;; (params random_seed 0)
...
$ rm -rf ./test-out-dir
```

#### check SMT seed is picked up

```sh
$ apalache-mc check --out-dir=./test-out-dir --length=0 --debug --tuning-options=smt.randomSeed=4242 Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ find ./test-out-dir/Counter.tla/* -type f -name log0.smt -exec cat {} \;
;; fp.spacer.random_seed = 4242
;; nlsat.seed = 4242
;; sat.random_seed = 4242
;; sls.random_seed = 4242
;; smt.random_seed = 4242
;; (params random_seed 4242)
...
$ rm -rf ./test-out-dir
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

### check View2.tla without --view

```sh
$ apalache-mc check --inv=Inv --max-error=10 View2.tla | sed 's/[IEW]@.*//'
...
Option maxError = 10 requires a view. None specified.
...
EXITCODE: ERROR (255)
```

### check bug #874

Unhandled `IllegalArgumentException` when accessing a non-existent field on a
record. With the old records, this spec was failing during model checking.
With the new records, this spec is failing at type checking.

See https://github.com/apalache-mc/apalache/issues/874

```sh
$ apalache-mc typecheck Bug874.tla | sed 's/[IEW]@.*//'
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
Bug931.tla:6:20-6:21: unexpected expression: Expected a non-polymorphic type, found: Set(b)
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

### check Bug1880.tla

```sh
$ apalache-mc check --length=1 Bug1880.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Bug1903.tla

```sh
$ apalache-mc check --length=1 Bug1903.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Bug2268.tla

```sh
$ apalache-mc check --length=1 --cinit=CInit Bug2268.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Bug2750.tla

```sh
$ apalache-mc check --config=Bug2750.cfg Bug2750.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (255)
```

### check Test2750.tla

```sh
$ apalache-mc check --config=Test2750.cfg Test2750.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check Bug2772.tla errors on unsupported syntax

It should not be possible to pass input, which would require function set expansion without triggering an exception.

```sh
$ apalache-mc check --inv=ErrInv --length=1 Bug2772.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (255)
```

### check Bug2772.tla succeeds on supported syntax

However, if one uses a semantically equivalent (syntactically different) expression, where the function set is not forced to expand, it should pass.

```sh
$ apalache-mc check --inv=OkInv --length=1 Bug2772.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```


### check profiling

Check that the profiler output is produced as explained in
[Profiling](https://apalache-mc.org/docs/apalache/profiling.html).

```sh
$ apalache-mc check --run-dir=./profile-run-dir --smtprof schroedinger_cat.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ head -n 1 ./profile-run-dir/profile.csv
# weight,nCells,nConsts,nSmtExprs,location
$ rm -rf ./profile-run-dir
```

### check y2k with --output-traces succeeds

```sh
$ apalache-mc check --out-dir=./test-out-dir --length=10 --output-traces --inv=Safety y2k_instance.tla | sed 's/I@.*//'
...
The outcome is: NoError
...
EXITCODE: OK
```

```sh
$ find ./test-out-dir/y2k_instance.tla/* -type f -exec basename {} \; | ./sort.sh
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

### check MC3_TwoPhaseTyped.tla succeeds

Test that variants are working as expected.

```sh
$ apalache-mc check --inv=TCConsistent --length=3 MC3_TwoPhaseTyped.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check OptionTests.tla succeeds

These tests check that the operators defined in `Option.tla` work as expected.

```sh
$ apalache-mc check --length=0 OptionTests.tla | sed 's/[IEW]@.*//'
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
Check the manual: https://apalache-mc.org/docs/apalache/parameters.html
Input error (see the manual): SubstRule: Variable N is not assigned a value
...
EXITCODE: ERROR (255)
```

### check Bug1058.tla reports no error: regression for #Bug1058

```sh
$ apalache-mc check Bug1058.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
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
Test928.tla:20:10-20:30: unexpected expression: Expected a non-polymorphic type, found: a
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

### check TestSets.tla reports an error on FailExpandLargePowerset

```sh
$ apalache-mc check --length=0 --inv=FailExpandLargePowerset TestSets.tla | sed 's/[IEW]@.*//'
...
<unknown>: known limitation: Attempted to expand a SUBSET of size 2^30, whereas the built-in limit is 2^20
...
EXITCODE: ERROR (255)
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

Disabled because fixing #2338 causes this to stack-overflow
Revisit once pointers are implemented.

<!-- $MDX skip -->
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
$ apalache-mc check --inv=TypeOK --length=1 RecMem1627.tla | sed 's/[IEW]@.*//'
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
$ apalache-mc check TestRecordsNew.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check MC_LamportMutexTyped.tla

Check the mutex algorithm with new records.

```sh
$ apalache-mc check --length=4 MC_LamportMutexTyped.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestVariants.tla

Variant operators work in the model checker.

```sh
$ apalache-mc check --inv=AllTests TestVariants.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check TestReqAckVariants.tla

```sh
$ apalache-mc check TestReqAckVariants.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check InfDomFun (array-encoding)

A regression test for functions with infinite domain.

```sh
$ apalache-mc check --inv=Inv InfDomFun.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (12)
```

### check Consensus_epr

A regression test for function operations.

```sh
$ apalache-mc check --inv=Safety Consensus_epr.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check FunExcept1 (array-encoding)

A regression test for EXCEPT.

```sh
$ apalache-mc check --inv=Sanity FunExcept1.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check FunExcept2 (array-encoding)

A regression test for EXCEPT.

```sh
$ apalache-mc check --inv=Sanity FunExcept2.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check FunExcept3 (array-encoding)

A regression test for EXCEPT.

```sh
$ apalache-mc check --inv=Sanity FunExcept3.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check FunInInfiniteSubset (array-encoding)

A regression test for function membership in the presence of infinite sets.

See https://github.com/apalache-mc/apalache/issues/2810

```sh
$ apalache-mc check --init=TypeOkay_ --inv=TypeOkay --length=1 FunInInfiniteSubset.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### check ERC20.tla

```sh
$ apalache-mc check --length=5 --inv=NoNegativeBalances MC_ERC20.tla | sed 's/I@.*//'
...
The outcome is: NoError
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
$ apalache-mc typecheck Empty.tla | sed 's/I@.*//'
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
$ apalache-mc typecheck Except617.tla | sed 's/[IEW]@.*//'
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

See https://github.com/apalache-mc/apalache/issues/860

```sh
$ apalache-mc typecheck Bug860.tla | sed 's/[IEW]@.*//'
...
Parsing error in the type annotation: (Int, Int) -> Bool
Typing input error: Parser error in type annotation of Op: '=>' expected but -> found
...
EXITCODE: ERROR (255)
```

### typecheck bug #832

Unhandled exception thrown due to incorrect annotation of a tuple return
type.

See https://github.com/apalache-mc/apalache/issues/832

```sh
$ apalache-mc typecheck Bug832.tla | sed 's/[IEW]@.*//'
...
Parsing error in the type annotation: () => (Bool, Bool)
Typing input error: Parser error in type annotation of Example: '->' expected but ) found
...
EXITCODE: ERROR (255)
```

### typecheck bug #925

Type unification should not recurse infinitely.

See: https://github.com/apalache-mc/apalache/issues/925

```sh
$ apalache-mc typecheck Bug925.tla | sed 's/[IEW]@.*//'
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
$ apalache-mc typecheck LamportMutexTyped.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### typecheck MC_LamportMutexTyped.tla

Typecheck a model checking instance.

```sh
$ apalache-mc typecheck MC_LamportMutexTyped.tla | sed 's/[IEW]@.*//'
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
$ apalache-mc typecheck TestRecordsNew.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### typecheck TestRecordsNewIll1.tla

No ill-typed record access.

```sh
$ apalache-mc typecheck TestRecordsNewIll1.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (120)
```

### typecheck TestRecordsNewIll2.tla

No ill-typed record access.

```sh
$ apalache-mc typecheck TestRecordsNewIll2.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (120)
```

### typecheck TestRecordsNewIll3.tla

No ill-typed record access.

```sh
$ apalache-mc typecheck TestRecordsNewIll3.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (120)
```

### typecheck TestRecordsNewIll4.tla

No ill-typed record access.

```sh
$ apalache-mc typecheck TestRecordsNewIll4.tla | sed 's/[IEW]@.*//'
...
EXITCODE: ERROR (120)
```

### typecheck TestVariants.tla

Variant operators are type correct.

```sh
$ apalache-mc typecheck TestVariants.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### typecheck TestReqAckVariants.tla

```sh
$ apalache-mc typecheck TestReqAckVariants.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### typecheck TestAliasOld.tla

```sh
$ apalache-mc typecheck TestAliasOld.tla | sed 's/[IEW]@.*//'
...
Operator TestAlias_aliases: Deprecated syntax in type alias OLD_ALIAS. Use camelCase of Type System 1.2.
...
EXITCODE: OK
```

### typecheck TestAliasNew.tla

```sh
$ apalache-mc typecheck TestAliasNew.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### typecheck TestAliasNewMissing.tla

```sh
$ apalache-mc typecheck TestAliasNewMissing.tla | sed 's/[IEW]@.*//'
...
Typing input error: Missing @typeAlias: newAlias = <type>;
...
EXITCODE: ERROR (255)
```

### typecheck TestUnsafeRecord.tla

```sh
$ apalache-mc typecheck TestUnsafeRecord.tla | sed 's/[IEW]@.*//'
...
[TestUnsafeRecord.tla:6:17-6:19]: Cannot apply R() to the argument "b" in R()["b"].
...
EXITCODE: ERROR (120)
```

### typecheck TestGetX.tla

```sh
$ apalache-mc typecheck TestGetX.tla | sed 's/[IEW]@.*//'
...
[TestGetX.tla:2:12-2:14]: Cannot apply r to the argument "x" in r["x"].
...
EXITCODE: ERROR (120)
```

### typecheck TestGetXWithRows.tla

```sh
$ apalache-mc typecheck TestGetXWithRows.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### typecheck PolyTooGeneral.tla

```sh
$ apalache-mc typecheck PolyTooGeneral.tla | sed 's/[IEW]@.*//'
...
[PolyTooGeneral.tla:6:1-6:10]: Id's type annotation ((c) => b) is too general, inferred: ((a) => a)
...
EXITCODE: ERROR (120)
```

### typecheck PrintTypes

```sh
$ apalache-mc typecheck PrintTypes.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### typecheck annotation with comments

Regression test for https://github.com/apalache-mc/apalache/issues/2163

```sh
$ apalache-mc typecheck CommentedTypeAnnotation.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### constant operators

#### typecheck ConstantOperator.tla

Test that typechecker supports first-order `CONSTANTS`.

Regression test for https://github.com/apalache-mc/apalache/issues/2388

```sh
$ apalache-mc typecheck ConstantOperator.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

#### typecheck ConstantOperatorImpl.tla

Test that typechecker supports substituting a first-order `CONSTANT` via
`INSTANCE`.

Regression test for https://github.com/apalache-mc/apalache/issues/2388

```sh
$ apalache-mc typecheck ConstantOperatorImpl.tla | sed 's/[IEW]@.*//'
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
log0.smt
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
05_OutTemporalPass.json
05_OutTemporalPass.tla
06_OutInlinePass.json
06_OutInlinePass.tla
07_OutPrimingPass.json
07_OutPrimingPass.tla
08_OutVCGen.json
08_OutVCGen.tla
09_OutPreprocessingPass.json
09_OutPreprocessingPass.tla
10_OutTransitionFinderPass.json
10_OutTransitionFinderPass.tla
11_OutOptimizationPass.json
11_OutOptimizationPass.tla
12_OutAnalysisPass.json
12_OutAnalysisPass.tla
detailed.log
log0.smt
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
05_OutTemporalPass.json
05_OutTemporalPass.tla
06_OutInlinePass.json
06_OutInlinePass.tla
07_OutPrimingPass.json
07_OutPrimingPass.tla
08_OutVCGen.json
08_OutVCGen.tla
09_OutPreprocessingPass.json
09_OutPreprocessingPass.tla
10_OutTransitionFinderPass.json
10_OutTransitionFinderPass.tla
11_OutOptimizationPass.json
11_OutOptimizationPass.tla
12_OutAnalysisPass.json
12_OutAnalysisPass.tla
detailed.log
log0.smt
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
$ rm -rf ./test-out-dir ./test-run-dir
```

## configuration management

### configuration management: read run-dir from local `.apalache.cfg`

```sh
$ echo "common.run-dir: ./configured-run-dir" > .apalache.cfg
$ apalache-mc check --length=0 Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ ls ./configured-run-dir | ./sort.sh
detailed.log
log0.smt
run.txt
$ rm -rf ./configured-run-dir ./.apalache.cfg
```

### configuration management: CLI config file overrides local `.apalache.cfg`

```sh
$ echo "common.run-dir: ./to-override-dir" > .apalache.cfg
$ echo "common.run-dir: ./configured-run-dir" > cli-config.cfg
$ apalache-mc check --config-file=cli-config.cfg --length=0 Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ ! test -d ./to-override-dir
$ test -d ./configured-run-dir
$ rm -rf ./configured-run-dir ./.apalache.cfg ./cli-config.cfg
```

### configuration management: CLI argument overrides config-file

```sh
$ echo "common.run-dir: ./to-override-dir" > cli-config.cfg
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
$ echo "common.run-dir: ~/run-dir" > .apalache.cfg
$ JVM_ARGS="-Duser.home=." apalache-mc check --length=0 Counter.tla | sed 's/[IEW]@.*//'
...
EXITCODE: OK
$ test -d ./run-dir
$ rm -rf ./run-dir ./.apalache.cfg
```

### configuration management: invalid features are rejected with error

```sh
$ echo "common.features: [ invalid-feature ]" > .apalache.cfg
$ apalache-mc check --length=0 Counter.tla | grep -o "Configuration error: .*'"
...
Configuration error: at 'common.features.0'
$ rm -rf ./.apalache.cfg
```

### configuration management: unsupported keys produce an error on load

```sh
$ echo "invalid.key: foo" > .apalache.cfg
$ apalache-mc check --length=0 Counter.tla | grep -o -e "Configuration error:.*" -e ".apalache.cfg:.*" -e "EXITCODE:.*"
...
Configuration error: at 'invalid':
.apalache.cfg: 1) Unknown key.
EXITCODE: ERROR (255)
$ rm -rf ./.apalache.cfg
```

### configuration management: derived configuration can be dumped to a file

First, set some custom config options, to ensure they'll be merged into the derived config:

```sh
$ printf "checker={length=0,inv=[Inv]}, common{out-dir=./cfg-out, features=[rows]}" > demo-config.cfg
```

Then, run a trivial checking command with `--debug` so the derived config will
be saved into to the `--run-dir`:

```sh
$ apalache-mc check --config-file=demo-config.cfg --run-dir=configdump-dir --debug Counter.tla
...
```

Finally, confirm that the dumped config looks as expected, and clean up:

```sh
$ cat ./configdump-dir/application-configs.cfg
checker {
    algo=incremental
    discard-disabled=true
    inv=[
        Inv
    ]
    length=0
    max-error=1
    no-deadlocks=false
    smt-encoding {
        type=oopsla-19
    }
    timeout-smt-sec=0
    tuning {
        "search.outputTraces"="false"
    }
}
common {
    command=check
    config-file="demo-config.cfg"
    debug=true
    features=[
        rows
    ]
    out-dir="./cfg-out"
    profiling=false
    run-dir=configdump-dir
    smtprof=false
    write-intermediate=false
}
input {
    source {
        file="Counter.tla"
        format=tla
        type=file
    }
}
output {}
server {
    port=8822
    server-type {
        type=checker-server
    }
}
tracee {}
typechecker {
    inferpoly=true
}
$ rm -rf ./configdump-dir ./demo-config.cfg ./cfg-out
```

## module lookup

### module lookup: looks up dummy module from standard library

```sh
$ cd module-lookup/subdir-no-dummy && apalache-mc parse --output=output.tla Including.tla
...
EXITCODE: OK
$ cat module-lookup/subdir-no-dummy/output.tla
-------------------------------- MODULE output --------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache, Variants

Init == TRUE

Next == TRUE

================================================================================
$ rm module-lookup/subdir-no-dummy/output.tla
```

### module lookup: looks up modules in the same directory

Regression test for https://github.com/apalache-mc/apalache/issues/426

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
The Apalache server is running on port 8822. Press Ctrl-C to stop.
...
```

### server mode: server can be started at different port

```sh
$ apalache-mc server --port=8888 & pid=$! && sleep 3 && kill $pid
...
The Apalache server is running on port 8888. Press Ctrl-C to stop.
...
```

### server mode: error is nicely reported when port is already in use

NOTE: These tests are skipped because the would complicate our CI process
more than is warranted by the functionality they test. To enable these tests,
remove the `$MDX skip` annotations.

Start socat in the background to occupy the port, save its pid and wait a second to let binding happen
<!-- $MDX skip -->
```sh
$ socat TCP-L:8888,fork,reuseaddr - & echo $! > pid.pid && sleep 1
```

Try to start the Apalache server on the occupied port,
redirect its output to the file,
save its exit code,
strip logger prompt 
and exit with status code of the server
<!-- $MDX skip -->
```sh
$ apalache-mc server --port=8888 1>out 2>out; ext=$? && cat out | sed -E 's/E@.*$//' && exit $ext
...
Error while starting Apalache server: Failed to bind to address 0.0.0.0/0.0.0.0:8888: Address already in use
[1]
```

Cleanup: kill socat and delete temporary files
<!-- $MDX skip -->
```sh
$ cat pid.pid | xargs kill -9
$ rm pid.pid out
```

## quint input

### quint input: quint spec can be checked

`booleans.qnt.json` updated via `make quint-fixtures`

```sh
$ apalache-mc check --init=init --next=step booleans.qnt.json | sed 's/[IEW]@.*//'
...
EXITCODE: OK
```

### quint input: bigints are deserialized correctly

Regression test for https://github.com/apalache-mc/quint/issues/1055

```sh
$ apalache-mc check --out-dir=./test-out-dir --init=init --next=step --inv=inv bigint.qnt.json
...
EXITCODE: ERROR (12)
[12]
$ grep State0 test-out-dir/bigint.qnt.json/*/violation.tla
State0 == balance = 100000000000
$ rm -rf ./test-out-dir
```
