------------------------------- MODULE Bug593 -------------------------------
\* Module used in https://github.com/informalsystems/apalache/issues/593
\* Test to see issue has been resolved

EXTENDS Integers, Bug593Aux

VARIABLE 
\* @type: [type: Str]; 
record

Init == record = [type |-> "B"]

Next ==
    LET result == Dummy IN
    UNCHANGED record
===============================================================================