# Running the Tool

**Opt in statistics programme**: if you opt in for statistics collection (off by default),
then every run of Apalache will submit anonymized statistics to
`tlapl.us`. See the details in [TLA+ Anonymized Execution Statistics](./statistics.md).

Apalache supports several modes of execution. You can run it with the `--help` option,
to see the complete list of modes and their invocation commands:

```bash
$ apalache-mc --help
```

The most important commands are as follows:

 - `parse` reads a TLA+ specification with the SANY parser and flattens it by
   instantiating all modules. It terminates successfully, if there are no parse
   errors. The input specification to `parse` may be given in standard TLA+ format, or in the [JSON serialization
   format][], while the outputs are produced in both formats.

 - `typecheck` performs all of the operations of `parse` and additionally runs the type checker Snowcat to infer
   the types of all expressions in the parsed specification. It terminates successfully, if there are no type errors.

 - `simulate` performs all of the operations of `typecheck` and additionally runs the model checker in simulation mode, which *randomly* picks a sequence of [actions](https://apalache.informal.systems/docs/apalache/assignments-in-depth.html#slices) and checks the invariants for the subset of all executions which only admit actions in the selected order. 
 It terminates successfully, if there are no invariant violations. 
 This command usually checks randomized symbolic runs much faster than the `check` command.

 - `check` performs all of the operations of `typecheck` and then runs the model checker in bounded model checking mode, which checks invariants for *all executions*, the length of which does not exceed the value specified by the `--length` parameter. 
   It terminates successfully, if there are no invariant violations.

 - `test` performs all of the operations of `check` in a mode that is designed to [test a single action](https://apalache.informal.systems/docs/adr/006rfc-unit-testing.html#32-testing-actions).

## 1. Model checker and simulator command-line parameters

### 1.1. Model checker command-line parameters

The model checker can be run as follows:

```bash
$ apalache-mc check [--config=filename] [--init=Init] [--cinit=ConstInit] \
    [--next=Next] [--inv=Inv1,...,Invn] [--length=10] \
    [--temporal=TemporalProp1,...,TemporalPropn] \
    [--algo=(incremental|offline)] \
    [--discard-disabled] [--no-deadlock] \
    [--tuning-options-file=filename] [--tuning-options=key1=val1:...:keyn=valn] \
    [--smt-encoding=(oopsla19|arrays)] \
    [--out-dir=./path/to/dir] \
    [--write-intermediate=(true|false)] \
    [--config-file=./path/to/file] \
    [--profiling=false] \
    [--output-traces=false] \
    <myspec>.tla
```

The arguments are as follows:

* General parameters:
    - `--config` specifies the [TLC configuration file](./tlc-config.md)
    - `--init` specifies the initialization predicate, *`Init` by default*
    - `--next` specifies the transition predicate, *`Next` by default*
    - `--cinit` specifies the constant initialization predicate, *optional*
    - `--inv` specifies the invariants to check, as a comma separated list, *optional*
    - `--length` specifies the maximal number of `Next` steps, *10 by default*
    - `--temporal` specifies the temporal properties to check, as a comma
      separated list, *optional*

* Advanced parameters:
    - `--algo` lets you to choose the search algorithm: `incremental` is using the incremental SMT solver, `offline` is
      using the non-incremental
      (offline) SMT solver
    - `--smt-encoding` lets you choose how the SMT instances are encoded: `oopsla19` (default) uses QF_UFNIA, and
      `arrays` (experimental) and `funArrays` (experimental) use SMT arrays with extensionality. This parameter can also
      be set via the `SMT_ENCODING` environment variable. See the [alternative SMT encoding using arrays] for details.
    - `--discard-disabled` does a pre-check on transitions and discard the disabled ones at every step. If you know that
      many transitions are always enabled, set it to false. Sometimes, this pre-check may be slower than checking the
      invariant. Default: true.
    - `--max-error <n>` instructs the search to stop after `n` errors, see [Enumeration of counterexamples][]. Default: 1.
    - `--view <name>` sets the state view to `<name>`, see [Enumeration of counterexamples][].
    - `--no-deadlock` disables deadlock-checking, when `--discard-disabled=false` is on. When `--discard-disabled=true`,
      deadlocks are found in any case.
    - `--tuning-options-file` specifies a properties file that stores options for
      [fine-tuning](tuning.md)
    - `--tuning-options` can pass and/or override these [fine-tuning](tuning.md)
      options on the command line
    - `--out-dir` set location for outputting any generated logs or artifacts,
      *`./_apalache-out` by default*
    - `--write-intermediate` if `true`, then additional output is generated. See
      [Detailed output](#detailed-output). *`false` by default*
    - `--run-dir=DIRECTORY` write all outputs directly into the specified
      `DIRECTORY`
    - `--config-file` a file to use for loading configuration parameters. This
      will prevent Apalache from looking for any local `.apalache.cfg` file.
    - `--profiling` (Bool): This flag governs the creation of `profile-rules.txt`
      used in [profiling](profiling.md). The file is only created if `profiling`
      is set to `True`.  Setting `profiling` to `False` is incompatible with the
      `--smtprof` flag. The default is `False`.
    - `--output-traces`: save an example trace for each symbolic run, default: `false`

Options passed with `--tuning-options` have priority over options passed with `--tuning-options-file`.

If an initialization predicate, transition predicate, or invariant is specified both in the configuration file, and on
the command line, the command line parameters take precedence over those in the configuration file.

In case conflicting arguments are passed for the same parameter, the following precedence order is followed:

1. Command-line value
2. Environment variable value
3. Configuration file value

### 1.2. Simulator command-line parameters

The simulator can be run as follows:

```bash
$ apalache-mc simulate
    [all-checker-options] [--max-run=NUM] <myspec>.tla
```

The arguments are as follows:

* Special parameters:

  - `--max-run=NUM`: but produce up to `NUM` simulation runs (unless `--max-error` errors have been found), default: `100`

### 1.3. Supplying JVM arguments

You can supply JVM argument to be used when running Apalache by setting the
environment variable `JVM_ARGS`. For example, to change the JVM heap size from
the default (`4096m`) to `1G` invoke Apalache as follows:

```sh
JVM_ARGS="-Xmx1G" apalache-mc <args>
```

If you are running Apalache via docker directly (instead of using the script in
`$APALACHE_HOME/script/run-docker.sh`), you'll also need to expose the
environment variable to the docker container:

```sh
$ JVM_ARGS="-Xmx1G" docker run -e JVM_ARGS --rm -v <your-spec-directory>:/var/apalache ghcr.io/informalsystems/apalache <args>
```

To track memory usage with: `jcmd <pid> VM.native_memory summary`, you can set

```
JVM_ARGS="-XX:NativeMemoryTracking=summary"
```

### 1.4. Bounded model checking

By default, Apalache performs *bounded model checking*, that is, it encodes a
symbolic execution of length `k` and a violation of a state invariant in SMT:

```tla
/\ Init[v_0/v]
/\ Next[v_0/v, v_1/v'] /\ Next[v_1/v, v_2/v'] /\ ... /\ Next[v_{k-1}/v, v_k/v']
/\ ~Inv[v_0/v] \/ ~Inv[v_1/v] \/ ... \/ ~Inv[v_k/v]
```

Here an expression `Inv[v_i/v]` means that the state variables `v` are replaced with their copies `v_i` for the
state `i`. Likewise, `Next[v_i/v,v_{i+1}/v']`
means that the state variables `v` are replaced with their copies `v_i` for the state `i`, whereas the state
variables `v'` are replaced with their copies
`v_{i+1}` for the state `i+1`.

**Bounded model checking is an incomplete technique**. If Apalache finds a bug
in this symbolic execution (by querying z3), then it reports a counterexample.
Otherwise, it reports that no bug was found up to the given length. If a bug
needs a long execution to get revealed, bounded model checking may miss it!

### 1.5. Checking an inductive invariant

To check executions of arbitrary lengths, one usually finds a formula that satisfies the two following properties:

```tla
/\ Init => TypeOK /\ IndInv
/\ TypeOK /\ IndInv /\ Next => TypeOK' /\ IndInv'
```

In normal words: (1) The initial states satisfy the constraint `TypeOK /\ IndInv`,
and (2) whenever the specification makes a step when starting in a state that satisfies `TypeOK /\ IndInv`,
it ends up in a state that again satisfies `TypeOK /\ IndInv`.

Note that we usually check `IndInv` in conjunction with `TypeOK`, as we have to constrain the variable values.
In the `y2k` example, our inductive invariant is actually constraining the variables.
In fact, such an inductive invariant is usually called `TypeOK`.

To check an inductive invariant ``IndInv`` in Apalache, you run two commands that check the above two formulas:

 - **IndInit**: Check that the initial states satisfy `IndInv`:

    ```bash
    $ apalache-mc check --init=Init --inv=IndInv --length=0 <myspec>.tla
    ```

 - **IndNext**: Check that `Next` does not drive us outside of `IndInv`:

    ```bash
    $ apalache-mc check --init=IndInv --inv=IndInv --length=1 <myspec>.tla
    ```

Usually, you look for an inductive invariant to check a safety predicate. For
example, if you have found an inductive invariant `IndInv` and want to check a
safety predicate `Safety`, you have to run Apalache once again:

 - **IndProp**: Check that all states captured with `IndInv` satisfy the predicate `Safety`:

    ```bash
    $ apalache-mc check --init=IndInv --inv=Safety --length=0 <myspec>.tla
    ```

It may happen that your inductive invariant `IndInv` is too weak and it
violates `Safety`. In this case, you would have to add additional constraints to `IndInv`.
Then you would have to check the queries IndInit, IndNext, and IndProp again.

## 2. Examples

### 2.1. Checking safety up to 20 steps

```bash
$ cd test/tla
$ apalache-mc check --length=20 --inv=Safety y2k_override.tla
```

This command checks, whether `Safety` can be violated in 20 specification steps. If `Safety` is not violated, your spec
might still have a bug that requires a computation longer than 20 steps to manifest.

### 2.2. Checking an inductive invariant:

```bash
$ cd test/tla
$ apalache-mc check --length=0 --init=Init --inv=Inv y2k_override.tla
$ apalache-mc check --length=1 --init=Inv  --inv=Inv y2k_override.tla
```

The first call to apalache checks, whether the initial states satisfy the invariant. The second call to apalache checks,
whether a single specification step satisfies the invariant, when starting in a state that satisfies the invariant. (
That is why these invariants are called inductive.)

### 2.3. Using a constant initializer:

```bash
$ cd test/tla
apalache-mc check --cinit=ConstInit --length=20 --inv=Safety y2k_cinit.tla
```

This command checks, whether `Safety` can be violated in 20 specification steps. The constants are initialized with the
predicate
`ConstInit`, defined in `y2k_cinit.tla` as:

```tla
ConstInit == BIRTH_YEAR \in 0..99 /\ LICENSE_AGE \in 10..99
```

In this case, Apalache finds a safety violation, e.g., for
`BIRTH_YEAR=89` and `LICENSE_AGE=10`. A complete counterexample is printed in `counterexample.tla`.

The final lines in the file clearly indicate the state that violates the invariant:

```tla
State14 ==
/\ BIRTH_YEAR = 89
/\ LICENSE_AGE = 10
/\ hasLicense = TRUE
/\ year = 0

(* The following formula holds true in the last state and violates the invariant *)

InvariantViolation == hasLicense /\ year - BIRTH_YEAR < LICENSE_AGE
```

<a name="lookup"></a>

## 3. Module lookup

Apalache uses [the SANY parser](https://lamport.azurewebsites.net/tla/tools.html), which is the standard parser of TLC
and the TLA+ Toolbox. By default, SANY is looking for modules (in this order) in

1. The current working directory.
2. The directory containing the main TLA+ file passed on the CLI.
3. A small Apalache standard library (bundled from `$APALACHE_HOME/src/tla`).
4. The Java package `tla2sany.StandardModules` (usually provided by the `tla2tools.jar` that is included in the Java
   classpath).

__Note:__ To let TLA+ Toolbox and TLC know about the Apalache modules, include
`$APALACHE_HOME/src/tla` in the lookup directories, as explained by Markus Kuppe for
the [TLA+ Community Modules](https://github.com/tlaplus/CommunityModules).

<a name="detailed"></a>

## 4. Detailed output

The location for detailed output is determined by the value of the `out-dir`
parameter, which specifies the path to a directory into which all Apalache
runs write their outputs (see [configuration instructions](config.md)).

Each run will produce a unique subdirectory inside its "namespace", derived from
the file name of the specification, using the following convention
`yyyy-MM-ddTHH-mm-ss_<UNIQUEID>`.

For an example, consider using the default location of the `run-dir` for a run of Apalache on a spec named `test.tla`.
This will create a directory structuring matching the following pattern:

```
./_apalache-out/
└── test.tla
    └── 2021-11-05T22-54-55_810261790529975561
```

The default value for the `out-dir` is the `_apalache-out` directory in the
current working directly. The subdirectory `test.tla` is derived from the name
of the spec on which the tool was run, and the run-specific subdirectory
`2021-11-05T22-54-55_810261790529975561` gives a unique location to write the
all the outputs produced by the run.

The tool only writes important messages on stdout, but a detailed log can be
found in the `detailed.log` in the run-specific subdirectory.

The directory also includes a file `run.txt`, reporting the command line
arguments used during the run.

Additionally, if the parameter `write-intermediate` is set to `true` (see
[configuration instructions](config.md)) each pass of the model checker produces
intermediate TLA+ files in the run-specific subdirectory:

- File `out-parser.tla` is produced as a result of parsing and importing into the intermediate representation, Apalache
  TLA IR.
- File `out-config.tla` is produced as a result of substituting CONSTANTS, as described
  in [Setting up specification parameters](./parameters.md).
- File `out-inline.tla` is produced as a result of inlining operator definitions and `LET-IN` definitions.
- File `out-priming.tla` is produced as a result of replacing constants and variables in `ConstInit` and `Init` with
  their primed versions.
- File `out-vcgen.tla` is produced as a result of extracting verification conditions, e.g., invariants to check.
- File `out-prepro.tla` is produced as a result of running all preprocessing steps.
- File `out-transition.tla` is produced as a result of finding assignments and symbolic transitions.
- File `out-opt.tla` is produced as a result of expression optimizations.
- File `out-analysis.tla` is produced as a result of analysis, e.g., marking Skolemizable expressions and expressions to
  be expanded.

<a name="parsing"></a>

## 5. Parsing and pretty-printing

If you'd like to check that your TLA+ specification is syntactically correct, without running the model checker, you can
run the following command:

```bash
$ apalache-mc parse <myspec>.tla
```

In this case, Apalache performs the following steps:

1. It parses the specification with [SANY](https://lamport.azurewebsites.net/tla/tools.html).

2. It translates SANY semantic nodes
   into [Apalache IR](https://github.com/informalsystems/apalache/blob/master/tlair/src/main/scala/at/forsyte/apalache/tla/lir/package.scala)
   .

3. If the `--write-intermediate` flag is given, it pretty-prints the IR into
   the output directory (see [Detailed output](#detailed)).

You can also write output to a specified location by using the `--output` flag.
E.g.,

```bash
$ apalache-mc parse --output=result.json <myspec>.tla
```

will write the IR to the file `result.json`.

[alternative SMT encoding using arrays]: ../adr/011adr-smt-arrays.md
[Enumeration of counterexamples]: ./principles/enumeration.md
[JSON serialization format]: ../adr/005adr-json.md
reads a TLA+ specification with the SANY parser and flattens it by
