# Top-level operator definitions

[[Back to user operators]](./user-operators.md)

## Quick example

Without going into details, here is a quick example of a top-level user
operator (which has to be defined in a module) and of its application:

```tla
----------------------- MODULE QuickTopOperator -------------------------------
...
Abs(i) == IF i >= 0 THEN i ELSE -i
...
B(k) == Abs(k)
===============================================================================
```

As you most probably guessed, the operator `Abs` expects one argument `i`.
Given an integer `j`, then the result of computing `Abs(j)` is the absolute
value of `j`. The same applies, when `j` is a natural number or a real number.

## Syntax of operator definitions

In general, operators of `n` arguments are
defined as follows:

```tla
\* an operator without arguments (nullary)
Opa0 == body_0

\* an operator of one argument (unary)
Opa1(param1) == body_1

\* an operator of two arguments (binary)
Opa2(param1, param2) == body_2
...
```

In this form, the operator arguments are not allowed to be operators. If you want
to receive an operator as an argument, see the syntax of [Higher-order operators].

Here are concrete examples of operator definitions:

```tla
----------------------------- MODULE FandC ------------------------------------
EXTENDS Integers
...

ABSOLUTE_ZERO_IN_CELCIUS ==
    -273

Fahrenheit2Celcius(t) ==
    (t - 32) * 10 / 18

Max(s, t) ==
    IF s >= t THEN s ELSE t
...
===============================================================================
```

*What is their arity (number of arguments)?*

If you are used to imperative languages such as Python or Java, then you are
probably surprised that operator definitions do not have any `return`
statement. The reason for that is simple: TLA+ is not executed on any hardware.
To understand how operators are evaluated, see the semantics below.

## Syntax of operator applications

Having defined an operator, you can apply it inside another operator as follows
(in a module):

```tla
----------------------------- MODULE FandC ------------------------------------
EXTENDS Integers
VARIABLE fahrenheit, celcius
\* skipping the definitions of
\* ABSOLUTE_ZERO_IN_CELCIUS, Fahrenheit2Celcius, and Max
...

UpdateCelcius(t) ==
    celcius' = Max(ABSOLUTE_ZERO_IN_CELCIUS, Fahrenheit2Celcius(t))

Next ==
    /\ fahrenheit' \in -1000..1000
    /\ UpdateCelcius(fahrenheit')
...    
===============================================================================
```

In the above example, you see examples of four operator applications:

  1. The nullary operator `ABSOLUTE_ZERO_IN_CELCIUS` is applied without any
  arguments, just by its name. Note how a nullary operator does not require
  parentheses `()`. Yet another quirk of TLA+.

  2. The one-argument operator Fahrenheit2Celcius is applied to `t`,
  which is a parameter of the operator `UpdateCelcius`.

  3. The two-argument operator `Max` is applied to `ABSOLUTE_ZERO_IN_CELCIUS`
  and `Fahrenheit2Celcius(t)`.

  4. The one-argument operator `UpdateCelcius` is applied to `fahrenheit'`,
  which is the value of state variable `fahrenheit` in the next state of the
  state machine. TLA+ has no problem applying the operator to `fahrenheit'` or
  to `fahrenheit`.

Technically, there are more than four operator applications in our example.
However, all other operators are the [standard
operators](./standard-operators.md). We do not focus on them here.

**Note on the operator order.** As you can see, we are applying operators after
they have been defined in a module. This is a general rule in TLA+: A name can
be only referred to, if it has been defined in the code before. TLA+ is not
the first language to impose that rule. For instance, [Pascal] had it too.

**Note on shadowing.** TLA+ does not allow you to use the same name as an
operator parameter, if it has been defined in the context of the operator
definition. For instance, the following is not allowed:

```tla
-------------------------- MODULE NoShadowing ---------------------------------
VARIABLE x

\* the following operator definition produces a semantic error:
\* the parameter x is shadowing the state variable x
IsZero(x) == x = 0
===============================================================================
```

There are a few tricky cases, where shadowing can actually happen, e.g., see
the operator `dir` in [SlidingPuzzles]. However, we recommend to keep things
simple and avoid shadowing at all.


## Semantics of operator application

Precise treatment of operator application is given on page 320 of [Specifying
Systems]. In a nutshell, operator application in TLA+ is a [Call by macro
expansion], though it is a bit smarter: It does not blindly mix names from the
operator's body and its application context. For example, the following
semantics by substitution is implemented in the [Apalache] model checker.

Here we give a simple explanation for non-recursive operators. Consider the
definition of an `n`-ary operator `A` and its application in the definition
of another operator `B`:

```tla
A(p_1, ..., p_n) == body_of_A
...
B(r_1, ..., r_k) ==
    ...
    A(e_1, ..., e_n)
    ...
```

The following three steps allow us to replace application of the operator `A`
in `B`:

  1. Change the names in the definition of `A` in such a way such they do not
  clash with the names in `B` (as well as with other names that may be used in
  `B`). This is the well-known technique of [Alpha conversion] in programming
  languages. This may also require renaming of the parameters `p_1, ..., p_n`.
  Let the result of alpha conversion be the following operator:
  ```tla
  uniq_A(uniq_p_1, ..., uniq_p_n) == body_of_uniq_A
  ```

  1. Substitute the expression `A(e_1, ..., e_n)` in the definition of `B` with
  `body_of_uniq_A`.

  1. Substitute the names `uniq_p_1, ..., uniq_p_n` with the expressions `e_1,
  ..., e_n`, respectively.

The above transformation is usually called [Beta reduction].

**Example.** Let's go back to the module `FandC`, which we considered above. By
applying the substitution approach several times, we transform `Next` in
several steps as follows:

  First, by substituting the body of `UpdateCelsius`:

  ```tla
    Next ==
        /\ fahrenheit' \in -1000..1000
        /\ celcius' = Max(ABSOLUTE_ZERO_IN_CELCIUS, Fahrenheit2Celcius(fahrenheit'))
  ```

  Second, by substituting the body of `Max`:

  ```tla
    Next ==
        /\ fahrenheit' \in -1000..1000
        /\ celcius' =
            IF ABSOLUTE_ZERO_IN_CELCIUS >= Fahrenheit2Celcius(fahrenheit')
            THEN ABSOLUTE_ZERO_IN_CELCIUS
            ELSE Fahrenheit2Celcius(fahrenheit')
  ```

  Third, by substituting the body of `Fahrenheit2Celcius` (twice):

  ```tla
    Next ==
        /\ fahrenheit' \in -1000..1000
        /\ celcius' =
            IF ABSOLUTE_ZERO_IN_CELCIUS >= (fahrenheit' - 32) * 10 / 18
            THEN ABSOLUTE_ZERO_IN_CELCIUS
            ELSE (fahrenheit' - 32) * 10 / 18
  ```

You could notice that we applied beta reduction syntactically from top to
bottom, like peeling an onion. We could do it in another direction: First
starting with the application of `Fahrenheit2Celcius`. This actually does not
matter, as long as our goal is to produce a TLA+ expression that is free of
user-defined operators. For instance, [Apalache] applies [Alpha conversion] and
[Beta reduction] to remove user-defined operator and then translates the TLA+
expression to SMT.


[Higher-order operators]: ./higher-order-operators.md
[Pascal]: https://en.wikipedia.org/wiki/Pascal_(programming_language)
[SlidingPuzzles]: https://github.com/tlaplus/Examples/blob/master/specifications/SlidingPuzzles/SlidingPuzzles.tla
[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html?back-link=user-operators.html
[Call by macro expansion]: https://en.wikipedia.org/wiki/Evaluation_strategy#Call_by_macro_expansion
[Alpha conversion]: https://en.wikipedia.org/wiki/Lambda_calculus#%CE%B1-conversion
[Beta reduction]: https://en.wikipedia.org/wiki/Lambda_calculus#%CE%B2-reduction
[Apalache]: https://apalache.informal.systems

