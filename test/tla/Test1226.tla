--------------------------- MODULE Test1226 -------------------------
(* Test that SetAsFun is working as expected *)
EXTENDS Apalache

VARIABLES
    \* @type: Str -> Int;
    strToInt,
    \* @type: Set(Int) -> Int;
    intsToInt,
    \* @type: (Str -> Int) -> Str;
    funToFun

Init ==
    /\ strToInt = SetAsFun({
         <<"a", 2>>,
         <<"b", 3>>
       })
    /\ intsToInt = SetAsFun({
         <<{1, 2}, 3>>,
         <<{4, 5, 6}, 7>>
       })
    \* we can easily construct functions of functions
    /\ funToFun = SetAsFun({
        <<
            SetAsFun({ <<"a", 2>>, <<"b", 3>> }),
            "x"
        >>,
        <<
            SetAsFun({ <<"c", 9>>, <<"d", 10>> }),
            "y"
        >>
       })

Next ==
    UNCHANGED <<strToInt, intsToInt, funToFun>>

Inv ==
    /\ (DOMAIN strToInt) = { "a", "b" }
    /\ strToInt["a"] = 2
    /\ strToInt["b"] = 3
    /\ (DOMAIN intsToInt) = { {1, 2}, {4, 5, 6} }
    /\ intsToInt[{1, 2}] = 3
    /\ intsToInt[{4, 5, 6}] = 7
    \* yes, you can do that in TLA+
    /\ (DOMAIN funToFun) = {
         SetAsFun({ <<"a", 2>>, <<"b", 3>> }),
         SetAsFun({ <<"c", 9>>, <<"d", 10>> })
       }
    /\ funToFun[SetAsFun({ <<"a", 2>>, <<"b", 3>> })] = "x"
    /\ funToFun[SetAsFun({ <<"c", 9>>, <<"d", 10>> })] = "y"

=====================================================================
