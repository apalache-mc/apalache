# Idiomatic TLA+

## Introduction

In this document, we collect specification idioms that aid us in writing TLA+
specifications that are:

1. understood by distributed system engineers,
1. understood by verification engineers, and
1. understood by automatic analysis tools such as the Apalache model checker.

If you believe, that the above points are contradictory when put together, it is
to some extent true. TLA+ is an extremely general specification language. As a
result, it is easy to write a short specification that leaves puzzled a human
reader. It is even easier to write a (syntactically correct) specification that
turns to dust any program reasoning about TLA+. 

Nevertheless, we find TLA+ to be quite useful for writing concise specifications
of distributed protocols at [Informal Systems](https://informal.systems). Other
specifications languages -- especially, those designed for software verification
-- would require us to introduce unnecessary book-keeping details that would
both obfuscate the protocols and make their verification harder. However, we do
not always need _"all power of mathematics"_, so we find it useful to introduce
additional structure in TLA+ specifications.

Below, we summarize the idioms that help us in maintaining that structure.  As a
bonus, these idioms usually aid the Apalache model checker in analyzing the
specifications. Our idioms are quite likely different from the original ideas of
Leslie Lamport (the author of TLA+). So it is useful to read Lamport's
[Specifying Systems]. Importantly, these are _idioms_, not the rules set in
stone. If you believe that one of those idioms does not work for you in your
specific setting, don't follow it.


## The idioms

__Idiom 1:__ [Let there be (few) assignments](assignments.md)

__Idiom 2:__ Isolate updates to VARIABLES

__Idiom 3:__ Limit non-determinism to actions

__Idiom 4:__ Introduce pure operators

__Idiom 5:__ Name convention for operator parameters

__Idiom 6:__ Use Boolean operators in actions, not `IF-THEN-ELSE`

__Idiom 7:__ `CHOOSE` smart, prefer `\E`

__Idiom 8:__ Do not over-structure

__Idiom 9:__ Do not over-modularize

__Idiom 10:__ Separate normal paths from error paths.

__Idiom 11:__ Do you really need those nice recursive operators?

__Idiom 12:__ Do you really need set cardinalities?

__Idiom 13:__ Do you really need integers?


[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html

