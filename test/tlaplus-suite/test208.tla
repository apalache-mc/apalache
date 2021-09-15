\* SANY2 test.
\* Test to make sure that all keywords are useable as record fields.

-------------------- MODULE test208 ----------------
bar == 17

LEMMA TRUE
PROPOSITION TRUE
ASSUMPTION TRUE

Foo == 
/\  bar.NEW \union  [bar EXCEPT !.NEW = 0]
/\  bar.SF_ \union  [bar EXCEPT !.SF_ = 0]
/\  bar.WF_ \union  [bar EXCEPT !.WF_ = 0]
/\  bar.THEN \union  [bar EXCEPT !.THEN = 0]
/\ bar.BY \union [bar EXCEPT !.BY = 0]      \* 68 XXXXXX
/\ bar.HAVE \union [bar EXCEPT !.HAVE = 0]
/\ bar.QED \union [bar EXCEPT !.QED = 0]
/\ bar.TAKE \union [bar EXCEPT !.TAKE = 0]

/\ bar.DEF \union [bar EXCEPT !.DEF = 0]
/\ bar.HIDE \union [bar EXCEPT !.HIDE = 0]
/\ bar.RECURSIVE \union [bar EXCEPT !.RECURSIVE = 0] \* XXXXX 82
/\ bar.USE \union [bar EXCEPT !.USE = 0]

/\ bar.DEFINE \union [bar EXCEPT !.DEFINE = 0]
/\ bar.PROOF \union [bar EXCEPT !.PROOF = 0]
/\ bar.WITNESS \union [bar EXCEPT !.WITNESS = 0]
/\ bar.PICK \union [bar EXCEPT !.PICK = 0]

/\ bar.DEFS \union [bar EXCEPT !.DEFS = 0]
/\ bar.PROVE \union [bar EXCEPT !.PROVE = 0]
/\ bar.SUFFICES \union [bar EXCEPT !.SUFFICES = 0]
/\ bar.NEW \union [bar EXCEPT !.NEW = 0]

/\ bar.LAMBDA \union [bar EXCEPT !.LAMBDA = 0]
/\ bar.LEMMA \union [bar EXCEPT !.LEMMA = 0]
/\ bar.PROPOSITION \union [bar EXCEPT !.PROPOSITION = 0]
/\ bar.STATE \union [bar EXCEPT !.STATE = 0]
/\ bar.ACTION \union [bar EXCEPT !.ACTION = 0]
/\ bar.TEMPORAL \union [bar EXCEPT !.TEMPORAL = 0]
/\ bar.VARIABLE \union [bar EXCEPT !.VARIABLE = 0]

/\ bar.OBVIOUS \union [bar EXCEPT !.OBVIOUS = 0]
/\ bar.OMITTED \union [bar EXCEPT !.OMITTED = 0]

/\ bar.ASSUME \union [bar EXCEPT !.ASSUME = 0]
/\ bar.ELSE \union [bar EXCEPT !.ELSE = 0]
/\ bar.LOCAL \union [bar EXCEPT !.LOCAL = 0]
/\ bar.UNION \union [bar EXCEPT !.UNION = 0]
     
/\ bar.ASSUMPTION \union [bar EXCEPT !.ASSUMPTION = 0]
/\ bar.ENABLED \union [bar EXCEPT !.ENABLED = 0]
/\ bar.MODULE \union [bar EXCEPT !.MODULE = 0]
/\ bar.VARIABLE \union [bar EXCEPT !.VARIABLE = 0]
   
/\ bar.AXIOM \union [bar EXCEPT !.AXIOM = 0]
/\ bar.EXCEPT \union [bar EXCEPT !.EXCEPT = 0]
/\ bar.OTHER \union [bar EXCEPT !.OTHER = 0]
/\ bar.VARIABLES \union [bar EXCEPT !.VARIABLES = 0]
  
/\ bar.CASE \union [bar EXCEPT !.CASE = 0]
/\ bar.EXTENDS \union [bar EXCEPT !.EXTENDS = 0]
/\ bar.SF_ \union [bar EXCEPT !.SF_ = 0]
/\ bar.WF_ \union [bar EXCEPT !.WF_ = 0]
      
/\ bar.CHOOSE \union [bar EXCEPT !.CHOOSE = 0]
/\ bar.IF \union [bar EXCEPT !.IF = 0]        \* XXXXX
/\ bar.SUBSET \union [bar EXCEPT !.SUBSET = 0]
/\ bar.WITH \union [bar EXCEPT !.WITH = 0]
 
/\ bar.CONSTANT \union [bar EXCEPT !.CONSTANT = 0]
/\ bar.IN \union [bar EXCEPT !.IN = 0]
/\ bar.THEN \union [bar EXCEPT !.THEN = 0]    \* XXXXX
               
/\ bar.CONSTANTS \union [bar EXCEPT !.CONSTANTS = 0]
/\ bar.INSTANCE \union [bar EXCEPT !.INSTANCE = 0]
/\ bar.THEOREM \union [bar EXCEPT !.THEOREM = 0] \* XXXXX
       
/\ bar.DOMAIN \union [bar EXCEPT !.DOMAIN = 0]
/\ bar.LET \union [bar EXCEPT !.LET = 0]
/\ bar.UNCHANGED \union [bar EXCEPT !.UNCHANGED = 0]
================================



THEOREM Bar == ASSUME NEW y, ASSUME TRUE PROVE FALSE
               PROVE  TRUE


THEOREM TRUE
 <1>1. TAKE x \in << a:: {}, {}>> 
 <1>2. <1>1!a
 <1>3. <1>1!1
 <1> QED


==================================================
a+b == <<a, b>>
THEOREM TRUE
<1>2 TRUE
  <33>1 HAVE ~ TRUE
  <33>2 TAKE Id, Id1
  <33>3 TAKE Id4 \in {1}, <<Id2, Id3>> \in {2}
  <33>123 FooBar == <<Id, Id1, Id4, Id2, Id3>>
  <33>4 WITNESS {1} 
  <33>5 WITNESS {1} \in {2}, {3}
  <33>-... PICK x : ~ FALSE
          <+>*.   PICK y \in {1} : ~ FALSE
          <*>* QED
  <33>7 PICK y \in {1} : <33>5!1!1 + <33>3!1
    PROOF <55>1... TRUE
          <*>2.... USE <33>5, <33>7!1!1, <33>7!(42)!<< DEF +
          <55>2 QED
  <33>7a Foo == << <33>7!(1)!<< , <33>7!>> >>
  <33>8 PICK z \in {1}, <<y1, z1>> \in {2} : ~ FALSE
  <33>9 PICK w, u : <<1, 2, 3>>
    <34>* DEFINE A == <<x, y, z, y1, z1, w, u>>
    <34>*. B == A!1
    <34> QED
  <33>44 DEFINE A == <<x, y, z, y1, z1, w, u>>
  <33>*. B == <33>9!(1,2)!3
  <33>. BBC(Op(_,_)) == Op(1,2)
        DD == BBC(<33>9!@)
  <33>22 ASSUME TRUE PROVE FALSE
  <33>  BBB == \A xxxx \in {} : TRUE
  <33>14. INSTANCE Test1
  <*>  AA == INSTANCE Test1
  <33>  B3 == AA!Foo3!Def2
  <*>a ASSUME FALSE PROVE TRUE 
  <33>b CASE TRUE
  <33>c SUFFICES TRUE
  <33>. SUFFICES ASSUME FALSE PROVE TRUE
  <33>2a. QED
<1>14 HAVE <<1, 2, 3>>
<1>14a havedef == <1>14!1!3
<*> TAKE Id7 \in {1}
<*> WITNESS {1} \in {2}
<*> PICK x2 \in {1}, y2 \in {2} : ~ FALSE
   <+> PICK x3, y3 : ~ FALSE
   <*>*. DEFINE A2 == 1
   <*>2 B2 == 17
   <*> ASSUME FALSE PROVE TRUE 
   <*> CASE TRUE
   <*> TRUE
   <*> SUFFICES ASSUME FALSE PROVE TRUE
   <2> QED
<1>... DEFINE A == 1
<1> B == 17
<1> INSTANCE Test1
<1> AA == INSTANCE Test2 WITH B <- 1
<1>3. QED

===============================

\* Foo == \A x , y, z : TRUE
\* Bar == \A x \in {}, y, z \in {}, <<u, v>> \in {} : TRUE
\* Inst(a) == INSTANCE Test1
\* Foo == Inst(7)!Bar1
THEOREM Thm2 == TRUE
 <1>2 QED
       PROOF USE <1>2
             QED
====================
 PROOF 
\* DEFINE Def1 == TRUE
 USE Thm2!:  \* DEF Thm2 , Inst!Bar2
\* Def2 == TRUE
 QED
\*   PROOF USE Def1 DEFS Def2
\*         QED
=================================
THEOREM Thm3 == FALSE
 PROOF DEFINE A == B
       PROVE /\ TRUE
             /\ 1=1
         BY Thm2
       QED
==========================================================
THEOREM 1
 PROOF QED
       PROOF OBVIOUS
=================================================
=============================================================================

BY [.]
USE DEF FALSE
HIDE 
<1>abc FALSE
      BY MODULE M DEF MODULE M, 2 [.]
A == B
DEFINE F == INSTANCE M
A[x \in S] == B
INSTANCE M
<1>2. QED
(********
  PROOF ASSUME TRUE PROVE FALSE
          <1>1. TRUE
          <1>2. QED
        HAVE TRUE
        QED
********)
=============================================================================
