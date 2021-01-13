# User-defined operators and recursive functions

_Like macros, to do a lot of things in one system step..._

User-defined operators in TLA+ may be confusing. At first, they look like
functions in programming languages. (Recall that [TLA+
functions](./functions.md) are more like dictionaries or hash maps, not
functions in PL.) Then you realize that operators such as `Init` and `Next` are
used as logic predicates. However, large specifications often contain operators
that are not predicates, but in fact are similar to pure functions in
programming languages: They are computing values over the system state but pose
no constraints over the system states. On top of that, there are [Recursive
functions] that syntactically looks very similar to
operators.

Recently, Leslie Lamport has extended the syntax of TLA+ operators in [TLA+
version 2], which supports recursive operators and lambda operators.  The
operator syntax that is described in [Specifying Systems] describes TLA+
version 1. This page summarizes the syntax of user-defined operators in
versions 1 and 2.

**Short digression**. The most important thing to understand about user-defined
operators is that they are normally used inside `Init` and `Next`. While the
operator `Init` describes the initial states, the operator `Next` describes a
single step of the system.  That is, these two operators are describing the
initial states and the possible transitions of the system, respectively. They
do not describe the whole system computation.  Most of the time, we are writing
*canonical specifications*, which are written in temporal logic as `Init /\
[][Next]_vars`. Actually, you do not have to understand temporal logic, in
order to write canonical specifications. A canonical specification is saying:
(1) Initialize the system as `Init` prescribes, and (2) compute system
transitions as `Next` prescribes. It also allows for stuttering, but this
belongs to [Advanced topics].

After the digression, you should now see that user-defined operators in TLA+
are (normally) describing a single step of the system. Hence, they should be
terminating. That is why user operators are often understood as macros.  The
same applies to [Recursive operator definitions]. They have to
terminate within a single system step.

**Quirks of TLA+ operators.** Below we summarize features of
user-defined operators that you would probably find unexpected:

  1. Some operators are used as predicates and some are used to compute
  values (*à la pure*).

  1. Operators may accept other operators as parameters. Such operators are
  called [Higher-order operator definitions].

  1. Although operators may be passed as parameters, they are not first-class
  citizens in TLA+. For instance, an operator cannot be returned as a result of
  another operator. Nor can an operator be assigned to a variable (only the result
  of its application may be assigned to a variable).

  1. Operators do not support [Currying]. That is, you can only apply an operator
  by providing values for all of its expected arguments.

  1. Operators can be nested. However, nested operators require a slightly
  different syntax. They are defined with LET-IN definitions.

**Details about operators.** We go in detail about different kinds of operators
and recursive functions below:

 - [Top-level operator definitions]

 - [LET-IN definitions]

 - [Higher-order operator definitions]

 - [Anonymous operator definitions]

 - [Recursive operator definitions]

 - [Local operator definitions]

 - [Recursive functions]



[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html?back-link=user-operators.html
[Advanced topics]: http://lamport.azurewebsites.net/tla/advanced.html?back-link=user-operators.html
[TLA+ version 2]: https://lamport.azurewebsites.net/tla/tla2-guide.pdf
[Currying]: https://en.wikipedia.org/wiki/Currying

[Top-level operator definitions]: ./user/top-level-operators.md
[LET-IN definitions]: ./user/let-in.md
[Higher-order operator definitions]: ./user/higher-order-operators.md
[Anonymous operator definitions]: ./user/lambdas.md
[Recursive operator definitions]: ./user/recursive-operators.md
[Local operator definitions]: ./user/local-operators.md
[Recursive functions]: ./user/recursive-functions.md

