#  Running the Tool

**Opt-in statistics programme**: if you opt-in for statistics collection (off
by default), then every run of Apalache will submit anonymized statistics to
`tlapl.us`.  See the details in [TLA+ Anonymized Execution
Statistics](./statistics.html).

##  Model checker command-line parameters

The model checker can be run as follows:

```bash
$ apalache check [--config=filename] [--init=Init] [--cinit=ConstInit] \
    [--next=Next] [--inv=Inv] [--length=10] [--algo=(incremental|offline)] \
    [--all-enabled] [--no-deadlock] [--tuning=filename] <myspec>.tla
```

The arguments are as follows:

  * General parameters:
    - `--config` specifies the [TLC configuration file](./tlc-config.md),
    the default name is `<myspec>.cfg`
    - `--init` specifies the initialization predicate, *`Init` by default*
    - `--next` specifies the transition predicate, *`Next` by default*
    - `--cinit` specifies the constant initialization predicate, *optional*
    - `--inv` specifies the invariant to check, *optional*
    - `--length` specifies the maximal number of `Next` steps, *10 by default*

  * Advanced parameters:
    - `--algo` lets you to choose the search algorithm: `incremental` is using
    the incremental SMT solver, `offline` is using the non-incremental
    (offline) SMT solver
    - `--all-enabled` lets you to skip the test of whether symbolic transitions
    are enabled and execute them unconditionally (in a sound way!).  If you
    know that many transitions are enabled, this speeds up model checking.
    - `--no-deadlock` disables deadlock-checking, when `--all-enabled` is on.
    Without `--all-enabled`, deadlocks are found in any case.
    - `--tuning` specifies the properties file that stores the options for
  [fine tuning](tuning.md)

If an initialization predicate, transition predicate, or invariant is specified both in the configuration file,
and on the command line, the command line parameters take precedence over those in the configuration file.

### Bounded model checking

By default, Apalache performs *bounded model checking*, that is,
it encodes a symbolic execution of length `k` and an invariant violation
in SMT:

```tla
/\ Init[v_0/v]
/\ Next[v_0/v, v_1/v'] /\ Next[v_1/v, v_2/v'] /\ ... /\ Next[v_{k-1}/v, v_k/v']
/\ ~Inv[v_0/v] \/ ~Inv[v_1/v] \/ ... \/ ~Inv[v_k/v]
```

Here an expression `Inv[v_i/v]` means that the state variables `v` are replaced
with their copies `v_i` for the state `i`.  Likewise, `Next[v_i/v,v_{i+1}/v']`
means that the state variables `v` are replaced with their copies `v_i` for the
state `i`, whereas the state variables `v'` are replaced with their copies
`v_{i+1}` for the state `i+1`.

#### Bounded model checking is an incomplete technique

If Apalache finds a bug in this symbolic execution (by querying z3), then it
reports a counterexample. Otherwise, it reports that no bug was found up to the
given length. If a bug needs a long execution to get revealed, bounded model
checking may miss it!


### Checking an inductive invariant

To check executions of arbitrary lengths, one usually finds a formula that
satisfies the two following properties:

```tla
/\ Init => TypeOK /\ IndInv
/\ TypeOK /\ IndInv /\ Next => TypeOK' /\ IndInv'
```

In normal words: (1) The initial states satisfy the constraint `TypeOK /\
IndInv`, and (2) whenever the specification makes a step when starting in a
state that satisfies `TypeOK /\ IndInv`, it ends up in a state that again
satisfies `TypeOK /\ IndInv`.

Note that we usually check `IndInv` in conjunction with `TypeOK`, as we
have to constrain the variable values. In the `y2k` example, our inductive
invariant is actually constraing the variables. In fact, such an inductive
invariant is usually called `TypeOK`.

To check an inductive invariant ``IndInv`` in Apalache, you run two commands
that check the above two formulas:

```bash
$ apalache check --init=Init --inv=IndInv --length=0 <myspec>.tla
```

and

```bash
$ apalache check --init=IndInv --inv=IndInv --length=1 <myspec>.tla
```

##  Examples

### Checking safety up to 20 steps

```bash
$ cd test/tla
$ apalache check --length=20 --inv=Safety y2k_override.tla
```

This command checks, whether `Safety` can be violated in 20 specification
steps. If `Safety` is not violated, your spec might still have a bug that
requires a computation longer than 20 steps to manifest.

### Checking an inductive invariant:

```bash
$ cd test/tla
$ apalache check --length=0 --init=Init --inv=Inv y2k_override.tla
$ apalache check --length=1 --init=Inv  --inv=Inv y2k_override.tla
```

The first call to apalache checks, whether the initial states
satisfy the invariant. The second call to apalache checks, whether
a single specification step satisfies the invariant, when starting
in a state that satisfies the invariant. (That is why these
invariants are called inductive.)

### Using a constant initializer:

```bash
$ cd test/tla
apalache check --cinit=ConstInit --length=20 --inv=Safety y2k_cinit.tla
```

This command checks, whether `Safety` can be violated in 20
specification steps. The constants are initialized with the predicate
`ConstInit`, defined in `y2k_cinit.tla` as:

```tla
ConstInit == BIRTH_YEAR \in 0..99 /\ LICENSE_AGE \in 10..99
```

In this case, Apalache finds a safety violation, e.g., for
`BIRTH_YEAR=89` and `LICENSE_AGE=10`. A complete counterexample
is printed in `counterexample.tla`.

The final lines in the file clearly indicate the state that violates the
invariant:

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
##  Module lookup

Apalache uses [the SANY
parser](https://lamport.azurewebsites.net/tla/tools.html), which is the
standard parser of TLC and TLA+ Toolbox. By default, SANY is looking for the
modules in the current working directory and in the Java package
`tla2sany.StandardModules`, which is usually provided by the `tla2tools.jar` that is
included in the Java classpath.

In addition to the modules in the current working directory, Appalache provides

- a small standard library (located in `$APALACHE_HOME/src/tla`), and
- support for additional source directories specified in the environment variable `TLA_PATH`. `TLA_PATH` should be a list of paths to directories separated by `:`. 

(Directories in the `TLA_PATH` are provided to SANY via the `TLA-Library` Java system variable.)    

So the module lookup order in Apalache is as follows:

1. The current working directory.
1. The directory `$APALACHE_HOME/src/tla`.
1. The directories specified in the environment variable `TLA_PATH`.
1. The Java package `tla2sany.StandardModules`.

__Note:__ To let TLA+ Toolbox and TLC know about the Apalache modules, include
`$APALACHE_HOME/src/tla` in the lookup directories, as explained by Markus
Kuppe for the [TLA+ Community
Modules](https://github.com/tlaplus/CommunityModules).

<a name="detailed"></a>
##  Detailed output

The tool will display only important messages on stdout, but a detailed log can
be found in `detailed.log`.

Additionally, each pass of the model checker produces an intermediate TLA+ file in
the run-specific directory `x/hh.mm-DD.MM.YYYY-<id>`:

  - File `out-parser.tla` is produced as a result of parsing and importing
    into the intermediate representation, Apalache TLA IR.
  - File `out-parser.json` is produced as a result of converting the
    Apalache TLA IR representation of the input into JSON format.
  - File `out-config.tla` is produced as a result of substituting CONSTANTS,
    as described in [Setting up specification parameters](./parameters.md).
  - File `out-inline.tla` is produced as a result of inlining operator
    definitions and `LET-IN` definitions.
  - File `out-priming.tla` is produced as a result of replacing constants and
    variables in `ConstInit` and `Init` with their primed versions.
  - File `out-vcgen.tla` is produced as a result of extracting verification
    conditions, e.g., invariants to check.
  - File `out-prepro.tla` is produced as a result of running all preprocessing
    steps.
  - File `out-transition.tla` is produced as a result of finding assignments
    and symbolic transitions.
  - File `out-opt.tla` is produced as a result of expression optimizations.
  - File `out-analysis.tla` is produced as a result of analysis, e.g.,
    marking Skolemizable expressions and expressions to be expanded.

<a name="parsing"></a>
##  Parsing and pretty-printing

If you'd like to check that your TLA+ specification is syntactically correct,
without running the model checker, you can run the following command:

```bash
$ apalache parse <myspec>.tla
```

In this case, Apalache performs the following steps:

1. It parses the specification with [SANY](https://lamport.azurewebsites.net/tla/tools.html).

1. It translates SANY semantic nodes into [Apalache IR](https://github.com/informalsystems/apalache/blob/master/tlair/src/main/scala/at/forsyte/apalache/tla/lir/package.scala).

1. It pretty-prints the IR into `out-parser.tla`, see [Detailed output](#detailed).
