---------------------------- MODULE Sequences ----------------------------
\*-------------- MODULE __rewire_sequences_in_apalache -----------------------
(**
 * ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ We have to call this module Sequences
 * in any case, otherwise, SANY complains.
 *
 * This file contains alternative definitions for the operators defined in
 * Sequences. Most importantly, we are adding type annotations. We also define
 * the Apalache-compatible behavior.
 *
 * These definitions are automatically rewired by the Apalache importer.
 *
 * Compare with the original definitions in Sequences.tla:
 *
 * https://github.com/tlaplus/tlaplus/blob/9310ee79efbebc700c4b84e8b805c35ab20161bb/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/Sequences.tla
 *)

(**
 * The infinite set of sequences whose elements come from the set S.
 * Apalache translates this operator to TlaSeqOper.seqSet.
 * However, the model checker does not support this operator.
 *
 * @type: Set(a) => Seq(a);
 *)
Seq(__S) ==
    \* Dummy definition. Apalache provides its own implementation.
    {}

(**
 * The sequence length.
 * Apalache translates this operator to TlaSeqOper.len.
 *
 * @type: Seq(a) => Int;
 *)
Len(__s) ==
    \* Dummy definition. Apalache provides its own implementation.
    0

(**
 * The sequence obtained by concatenating sequences s and t.
 * Apalache translates this operator to TlaSeqOper.concat.
 *
 * @type: (Seq(a), Seq(a)) => Seq(a) ;
 *)
__s \o __t ==
    \* Dummy definition. Apalache provides its own implementation.
    <<>>

(**
 * The sequence obtained by appending element e to the end of sequence s.
 * Apalache translates this operator to TlaSeqOper.append.
 *
 * @type: (Seq(a), a) => Seq(a);
 *)
Append(__s, __e) ==
    \* Dummy definition. Apalache provides its own implementation.
    <<>>

(**
 * The first element of a sequence.
 * If the sequence is empty, the result is undefined.
 * Apalache translates this operator to TlaSeqOper.head.
 *
 * @type: Seq(a) => a;
 *)
Head(__s) == __s[1]    

(**
 * The sequence <<s[m], s[m+1], ... , s[n]>>.
 *
 * @type: (Seq(a), Int, Int) => Seq(a);
 *)
SubSeq(__s, __m, __n) ==
    \* Dummy definition. Apalache provides its own implementation.
    <<>>

(**
 * The tail of a sequence.
 * Apalache translates this operator to TlaSeqOper.tail.
 * Note that Tail(s) in Sequences.tla does not define Tail(<<>>),
 * whereas Apalache does.
 *
 * @type: Seq(a) => Seq(a);
 *)
Tail(__s) ==
    \* Dummy definition. Apalache provides its own implementation.
    <<>>

\* instantiate __apalache_folds to use it in SelectSeq
LOCAL INSTANCE __apalache_folds    

(**
 * The subsequence of s consisting of all elements s[i] such that
 * Test(s[i]) is true.
 * Apalache uses the TLA+ definition via FoldSeq.
 *
 * @type: (Seq(a), a => Bool) => Seq(a);
 *)
SelectSeq(__s, __Test(_)) ==
    LET __AppendIfTest(__res, __e) ==
        IF __Test(__e)
        THEN Append(__res, __e)
        ELSE __res
    IN
    __ApalacheFoldSeq(__AppendIfTest, <<>>, __s)

===============================================================================
