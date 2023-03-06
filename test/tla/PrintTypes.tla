---- MODULE PrintTypes ----
\* Tests that the Snowcat type checker accepts all of the following
\* print statements, all of which TLC accepts.

EXTENDS TLC

VARIABLES
    \* @type: Str;
    a,
    \* @type: Bool;
    b,
    \* @type: Int;
    c,
    \* @type: Set(Str);
    d,
    \* @type: Seq(Str);
    e,
    \* @type: { x: Str, y: Str };
    f

Init ==
    /\ a = "hello world"
    /\ b = TRUE
    /\ c = 0
    /\ d = {"hello", "world"}
    /\ e = <<"hello", "world">>
    /\ f = [x |-> "hello", y |-> "world"]

Next ==
    /\ a = Print("", "hello world")
    /\ b = Print("", TRUE)
    /\ c = Print("", 0)
    /\ d = Print("", {"hello", "world"})
    /\ e = Print("", <<"hello", "world">>)
    /\ f = Print("", [x |-> "hello", y |-> "world"])
    /\ a = Print(a, "hello world")
    /\ b = Print(b, TRUE)
    /\ c = Print(c, 0)
    /\ d = Print(d, {"hello", "world"})
    /\ e = Print(e, <<"hello", "world">>)
    /\ f = Print(f, [x |-> "hello", y |-> "world"])
    /\ PrintT(a)
    /\ PrintT(b)
    /\ PrintT(c)
    /\ PrintT(d)
    /\ PrintT(e)
    /\ PrintT(f)
    /\ UNCHANGED <<a, b, c, d, e, f>>

Spec == Init /\ [][Next]_<<a, b, c, d, e, f>>


====