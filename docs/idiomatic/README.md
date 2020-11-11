# Idiomatic TLA+

**Authors:** Shon Feder, Igor Konnov + (who likes to contribute?)

_This document is under construction.
If you like to contribute, open a pull request._

## Introduction

In this document, we collect specification idioms that aid us in writing TLA+
specifications that are:

1. understood by distributed system engineers,
1. understood by verification engineers, and
1. understood by automatic analysis tools such as the Apalache model checker.

If you believe, that the above points are contradictory when put together, it is
to some extent true. TLA+ is an extremely general specification language. As a
result, it is easy to write a short specification that leaves a human reader
puzzled . It is even easier to write a (syntactically correct) specification that
turns any program trying to reason about TLA+ to dust. 

Nevertheless, we find TLA+ quite useful when writing concise specifications of
distributed protocols at [Informal Systems]. Other specification languages --
especially, those designed for software verification -- would require us to
introduce unnecessary book-keeping details that would both obfuscate the
protocols and make their verification harder. However, we do not always need
_"all the power of mathematics"_, so we find it useful to introduce additional
structure in TLA+ specifications.

Below, we summarize the idioms that help us in maintaining that structure.  As
a bonus, these idioms usually aid the Apalache model checker in analyzing the
specifications. Our idioms are quite likely different from the original ideas
of [Leslie Lamport] (the author of TLA+).
So it is useful to read Lamport's [Specifying Systems]. Importantly, these are
_idioms_, not rules set in stone. If you believe that one of those idioms
does not work for you in your specific setting, don't follow it.

If this is the first page where you encounter the word "TLA+", we do not
recommend that you continue to read the material. It is better to start with [The TLA+
Video Course](http://lamport.azurewebsites.net/video/videos.html) by Leslie
Lamport.  Once you have understood the basics and tried the language, it makes
sense to ask the question: "How do I write a specification that other people
understand?".  We believe that many TLA+ users reinvent rules that are
similar to our idioms.  By providing you with a bit of guidance, we hope to
reduce your discomfort when learning more advanced TLA+.


## The idioms

__Idiom 0:__
    [Keep state variables to the minimum](000keep-minimum-state-variables.md) :battery:

__Idiom 1:__ [Update state variables with assignments](001assignments.md) :date:

__Idiom 2:__ [Apply primes only to state variables](002primes.md) :pushpin:

__Idiom 3:__ Isolate updates to VARIABLES :ghost:

__Idiom 4:__ Isolate non-determinism in actions :crystal_ball:

__Idiom 5:__ Introduce pure operators :see_no_evil:

__Idiom 6:__ Introduce a naming convention for operator parameters :passport_control:

__Idiom 7:__ Use Boolean operators in actions, not `IF-THEN-ELSE` :no_good:

__Idiom 8:__ `CHOOSE` smart, prefer `\E` :guardsman:

__Idiom 9:__ Do not over-structure :microscope:

__Idiom 10:__ Do not over-modularize :duck:

__Idiom 11:__ Separate normal paths from error paths. :zap:

__Idiom 12:__ Do you really need those nice recursive operators? :cyclone:

__Idiom 13:__ Do you really need set cardinalities? :pizza:

__Idiom 14:__ Do you really need integers? :1234:


[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html
[Leslie Lamport]: https://lamport.azurewebsites.net/
[Informal Systems]: https://informal.systems
