# ADR-004: Syntax for Java-like annotations in TLA+ comments

| author      | revision |
| ----------- | --------:|
| Igor Konnov |        2 | 

This ADR documents our decision on using Java-like annotations in comments.
Our main motivation to have annotations is to simplify type annotations, as
presented in [ADR-002][]. Hence, in the following text, we are using
examples for type annotations. However, the annotations framework is not
restricted to types. Similar to Java and Scala, we can use annotations
to decorate operators with hints, which may aid the model checker.

## 1. What can be annotated

Annotations should be written in comments that are written in front of a
declaration. The following declarations are supported:
 
 1. Constant declarations, e.g., `CONSTANT N`.
 1. Variable declarations, e.g., `VARIABLE x`.
 1. Operator declarations, including:
   1. Top-level operator declarations, e.g., `Foo(x) == e`.
   1. Operators defined via LET-IN, e.g., `Foo(x) == LET Inner(y) == e IN f`.
   1. Recursive operators, e.g., `RECURSIVE Fact(_) Fact(n) == ...`
 1. Recursive and non-recursive functions including:
   1. Top-level functions, e.g., `foo[i \in Int] == e`.
   2. Functions defined via LET-IN, e.g.,`Foo == LET foo[i \in Int] == e IN f`

For an example, see Section 3.


## 2. Annotations syntax

An annotation is a string that follows the grammar (question mark denotes
optional rules):

```
Annotation  ::= '@' javaIdentifier ( '(' ArgList? ')' | ':' inlineArg ';' )?
ArgList     ::= (Arg) ( ',' Arg )*
Arg         ::= (string | integer | boolean)
inlineArg   ::= <char sequence excluding ';'>
string      ::= '"' <char sequence> '"'
integer     ::= '-'? [0-9]+
boolean     ::= ('false' | 'true')
```

Java Language Specification defines how a [Java identifier] looks like.
The sequence `<char sequence>` is a sequence admitted by [JavaTokenParsers]:
  
  - Any character except double quotes, control characters or backslash `\`
  - A backslash followed by another backslash, a single or double quote,
    or one of the letters `b`, `f`, `n`, `r` or `t`
  - `\` followed by u followed by four hexadecimal digits
  
**Examples.** The following strings are examples of syntactically correct
annotations:

 1. `@tailrec`
 1. `@type("(Int, Int) => Int")`
 1. `@type: (Int, Int) => Int ;`
 1. `@random(true)`
 1. `@deprecated("Use operator Foo instead")`
 1. `@range(0, 100)`

The above examples are just syntactically correct. Their meaning, if there is
any, is defined by the tool that is reading these annotations. Note that the
example 3 is not following the syntax of Java annotations. We have introduced
this format for one-argument annotations, especially, for type annotations.
Its purpose is to reduce the visual clutter in annotations that accept a string
as their only argument.

## 3. An annotated specification

The following specification shows how to write annotations, so they can be
correctly parsed by the SANY parser and Apalache. Note the location of comments
in front of: local operators, LET-definitions, and recursive operators.
Although these locations may seem to be suboptimal, this is how the SANY
parser locates comments that precede declarations.

```tla
-------------------------- MODULE Annotations ---------------------------------
EXTENDS Integers

CONSTANT
  \* @type: Int;
  N

VARIABLE
  \* the single-argument annotation
  \* @type: Set(Int);
  set

\* @pure
\* using the Java annotations, a bit verbose:
\* @type(" Int => Int ")
Inc(n) == n + 1

\* @type: Int => Int;
LOCAL LocalInc(x) == x + 1

A(n) ==
  LET \* @pure
      \* @type: Int => Int;
      Dec(x) == x + 1
  IN
  Dec(n)

RECURSIVE Fact(_)
\* @tailrec
\* @type: Int => Int;
Fact(n) ==
  IF n <= 1 THEN 1 ELSE n * Fact(n - 1)

\* @tailrec
\* @type: Int -> Int;
FactFun[n \in Int] ==
  IF n <= 1 THEN 1 ELSE n * FactFun[n - 1]

===============================================================================
```

## 4. Implementation

The implementation of the annotation parser can be found in the class
`at.forsyte.apalache.io.annotations.AnnotationParser` of the module
`tla-import`. (TODO: place a link when the PR is merged).

## 5. Discussion

Most likely, this topic does not deserve much discussion, as we are using
the pretty standard syntax of Java annotations. So we are following the
principle of the least surprise.

We also support the concise syntax for the annotations that accept a string as
a simple argument. For these annotations, we had to add the end marker ';'.
This is done because the SANY parser is pruning the linefeed character `\n`,
so it would be otherwise impossible to find the end of an annotation.


[ADR-002]: https://apalache.informal.systems/docs/adr/002adr-types.html
[JavaTokenParsers]: https://www.scala-lang.org/api/2.12.2/scala-parser-combinators/scala/util/parsing/combinator/JavaTokenParsers.html
[Java identifier]: https://docs.oracle.com/javase/specs/jls/se7/html/jls-3.html#jls-3.8

