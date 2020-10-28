------------------- MODULE Inst2 ----------------------
VARIABLE x
------------------- MODULE Inside ---------------------
VARIABLE y
Zero == 0

Init == y = Zero
Next == UNCHANGED y
===================================================
Zero == 1
I == INSTANCE Inside WITH y <- x

Init == I!Init
Next == I!Next

Inv == x = 0 
===================================================
