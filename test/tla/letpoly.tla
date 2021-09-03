------------------------------- MODULE letpoly -------------------------------
\* A test that shows that parametric types can be instantiated.
\* This test requires the type checker to support let polymorphism.
VARIABLE 
\* @type: Str -> Int;
strToInt,
\* @type: Int -> Str;
intToStr

\* Extend a function with a key -> value mapping
\* @type: (a -> b, a, b) => a -> b;
Extend(fun, key, value) == 
    [ k \in DOMAIN fun \union {key} |->
        IF k = key THEN value ELSE fun[k] ]

Init == 
  /\ strToInt = [ s \in {} |-> 0 ]
  /\ intToStr = [ i \in {} |-> "" ]

Next ==
  \* in the line below, Extend should accept Str -> Int, Str, and Int
  /\ strToInt' = Extend(strToInt, "a", 1)
  \* in the line below, Extend should accept Int -> Str, Int, and Str
  /\ intToStr' = Extend(intToStr, 1, "a")
    
===============================================================================
