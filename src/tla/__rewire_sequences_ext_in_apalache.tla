------------------------ MODULE SequencesExt ---------------------------------
\*------ MODULE __rewire_sequences_ext_in_apalache -----------------------
(**
 * ^^^^^^^^^^^^^^^^^^^^^^ We have to call this module SequencesExt in any
 * case, otherwise, SANY complains.
 *
 * This file contains alternative definitions for the operators defined in
 * SequencesExt. Most importantly, we are adding type annotations. We also
 * define the Apalache-compatible behavior.
 *
 * These definitions are automatically rewired by the Apalache importer.
 *
 * Compare with the original definitions in SequencesExt.tla:
 *
 * https://github.com/tlaplus/CommunityModules/blob/master/modules/SequencesExt.tla
 *)

LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE __apalache_folds
LOCAL INSTANCE __apalache_internal

(**
 * The image of the given sequence s. Cardinality(ToSet(s)) <= Len(s)
 * see https://en.wikipedia.org/wiki/Image_(mathematics)
 *
 * @type: Seq(a) => Set(a);
 *)
ToSet(__s) ==
  { __s[__i] : __i \in DOMAIN __s }

(**
 * Convert a set to some sequence that contains all the elements of the
 * set exactly once, and contains no other elements.
 *
 * @type: Set(a) => Seq(a);
 *)
SetToSeq(__S) == 
  LET __add_to_seq(__seq, __elem) == Append(__seq, __elem) IN
  __ApalacheFoldSet(__add_to_seq, <<>>, __S)

(**
 * Convert a set to a sorted sequence that contains all the elements of
 * the set exactly once, and contains no other elements.
 *
 * @type: (Set(a), (a, a) => Bool) => Seq(a);
 *)
SetToSortSeq(__S, __LessThan(_, _)) ==
  \* insert a new element element 
  LET \* @type: (Seq(b), b) => Seq(b);
        __insert_sorted(__seq, __newElem) ==
    LET __next_len == Len(__seq) + 1 IN
    \* find the position for inserting the element at
    LET __insertion_pos ==
      CHOOSE __p \in (DOMAIN __seq) \union { __next_len }:
        \A __i \in DOMAIN __seq:
          __i < __p <=> __LessThan(__seq[__i], __newElem)
    IN
    \* copy the sequence elements or insert a new one
    LET __copy_or_set(__i) ==
      IF __i < __insertion_pos
      THEN __seq[__i]
      ELSE IF __i = __insertion_pos
           THEN __newElem
           ELSE __seq[__i - 1]
    IN
    \* raw_seq may be longer than required
    LET __raw_seq == 
      __ApalacheMkSeq(__ApalacheSeqCapacity(__seq) + 1, __copy_or_set)
    IN
    \* prune the longer seq
    SubSeq(__raw_seq, 1, __next_len)
  IN
  __ApalacheFoldSet(__insert_sorted, <<>>, __S)

(**
 * TupleOf(s, 3) = s \X s \X s
 *
 * This operator is not well-typed.
 * Hence, we assign a reasonable type signature.
 *
 * @type: (Set(a), Int) => (Int -> Set(a));
 *)
TupleOf(__set, __n) == 
  __NotSupportedByModelChecker("TupleOf")

(**
 * All sequences up to length n with all elements in set.  Includes empty
 * sequence.
 *
 * Apalache does not support this operator. Try Apalache!Gen instead.
 *
 * @type: (Set(a), Int) => Set(Seq(a));
 *)
SeqOf(__set, __n) == 
  __NotSupportedByModelChecker("SeqOf")

(**
 * An alias for SeqOf to make the connection to Sequences!Seq, which is
 * the unbounded version of BoundedSeq.
 *
 * Apalache does not support this operator. Try Apalache!Gen instead.
 *
 * @type: (Set(a), Int) => Set(Seq(a));
 *)
BoundedSeq(__S, __n) ==
  __NotSupportedByModelChecker("BoundedSeq")

(**
 * TRUE iff the element e \in ToSet(s).
 *
 * @type: (Seq(a), a) => Bool;
 *)
Contains(__s, __e) ==
  \E __i \in DOMAIN __s:
    __s[__i] = __e

(**
 * Reverse the given sequence s:  Let l be Len(s) (length of s).
 * Equals a sequence s.t. << s[l], s[l - 1], ..., s[1]>>.
 *
 * @type: Seq(a) => Seq(a);
 *)
Reverse(__s) ==
  LET __s_len == Len(__s) IN
  LET __get_ith(__i) == __s[__s_len - __i + 1] IN
  SubSeq(__ApalacheMkSeq(__ApalacheSeqCapacity(__s), __get_ith), 1, __s_len)

(**
 * The sequence s with e removed or s iff e \notin Range(s).
 *
 * @type: (Seq(a), a) => Seq(a);
 *)
Remove(__seq, __e) ==
    LET __append_if_eq(__res, __t) ==
        IF __t /= __e
        THEN Append(__res, __t)
        ELSE __res
    IN
    __ApalacheFoldSeq(__append_if_eq, <<>>, __seq)

(**
 * Equals the sequence s except that all occurrences of element old are
 * replaced with the element new.
 *
 * @type: (Seq(a), a, a) => Seq(a);
 *)
ReplaceAll(__seq, __old, __new) ==
  LET __copy_or_set(__i) ==
    IF __seq[__i] = __old THEN __new ELSE __seq[__i]
  IN
  SubSeq(__ApalacheMkSeq(__ApalacheSeqCapacity(__seq), __copy_or_set),
        1, Len(__seq))
  
(**  
 * Inserts element e at the position i moving the original element to i+1
 * and so on.  In other words, a sequence t s.t.:
 *   /\ Len(t) = Len(s) + 1
 *   /\ t[i] = e
 *   /\ \A j \in 1..(i - 1): t[j] = s[j]
 *   /\ \A k \in (i + 1)..Len(s): t[k + 1] = s[k]
 *
 * @type: (Seq(a), Int, a) => Seq(a);
 *)
InsertAt(__seq, __k, __e) ==
  LET __copy_or_set(__i) ==
    IF __i = __k
    THEN __e
    ELSE IF __i < __k
         THEN __seq[__i]
         ELSE __seq[__i - 1]
  IN
  SubSeq(__ApalacheMkSeq(__ApalacheSeqCapacity(__seq) + 1, __copy_or_set),
        1, Len(__seq) + 1)

(**
 * Replaces the element at position i with the element e.
 *
 * @type: (Seq(a), Int, a) => Seq(a);
 *)
ReplaceAt(__s, __i, __e) ==
  [__s EXCEPT ![__i] = __e]  

(**
 * Removes the element at position i shortening the length of s by one.
 *
 * @type: (Seq(a), Int) => Seq(a);
 *)
RemoveAt(__s, __i) == 
  SubSeq(__s, 1, __i - 1) \o SubSeq(__s, __i + 1, Len(__s))

-----------------------------------------------------------------------------

(**
 * Cons prepends an element at the beginning of a sequence.
 *
 * @type: (a, Seq(a)) => Seq(a);
 *)
Cons(__elt, __seq) == 
    <<__elt>> \o __seq

(**
 * The sequence formed by removing its last element.
 *
 * @type: Seq(a) => Seq(a);
 *)
Front(__seq) == 
  SubSeq(__seq, 1, Len(__seq) - 1)

(**
 * The last element of the sequence.
 *
 * @type: Seq(a) => a;
 *)
Last(__seq) ==
  __seq[Len(__seq)]

-----------------------------------------------------------------------------

(**
 * TRUE iff the sequence s is a prefix of the sequence t, s.t.
 * \E u \in Seq(Range(t)) : t = s \o u. In other words, there exists
 * a suffix u that with s prepended equals t.
 *
 * @type: (Seq(a), Seq(a)) => Bool;
 *)
IsPrefix(__s, __t) ==
  __s = SubSeq(__t, 1, Len(__s))

(**
 * TRUE iff the sequence s is a prefix of the sequence t and s # t
 *
 * @type: (Seq(a), Seq(a)) => Bool;
 *)
IsStrictPrefix(__s,__t) ==
  IsPrefix(__s, __t) /\ __s # __t

(**
 * TRUE iff the sequence s is a suffix of the sequence t, s.t.
 * \E u \in Seq(Range(t)) : t = u \o s. In other words, there exists a
 * prefix that with s appended equals t.
 *
 * @type: (Seq(a), Seq(a)) => Bool;
 *)
IsSuffix(__s, __t) ==
  IsPrefix(Reverse(__s), Reverse(__t))

(**
 * TRUE iff the sequence s is a suffix of the sequence t and s # t
 *
 * @type: (Seq(a), Seq(a)) => Bool;
 *)
IsStrictSuffix(__s, __t) ==
  IsSuffix(__s,__t) /\ __s # __t
  
-----------------------------------------------------------------------------

(**
 * The set of prefixes of the sequence s, including the empty sequence.
 *
 * @type: Seq(a) => Set(Seq(a));
 *)
Prefixes(__s) ==
  { SubSeq(__s, 1, __l): __l \in { 0 } \union DOMAIN __s }

(**
 * The set of all sequences that are prefixes of the set of sequences S.
 *
 * @type: Set(Seq(a)) => Set(Seq(a));
 *)
CommonPrefixes(__S) ==
  \* TODO: use FoldSet?
  LET __P == UNION { Prefixes(__seq) : __seq \in __S }
  IN { __prefix \in __P: \A __t \in __S: IsPrefix(__prefix, __t) }

(**
 * The longest common prefix of the sequences in the set S.
 *
 * @type: Set(Seq(a)) => Seq(a);
 *)
LongestCommonPrefix(__S) ==
  CHOOSE __longest \in CommonPrefixes(__S):
      \* there can only be one LCP => CHOOSE
      \A __other \in CommonPrefixes(__S):
          Len(__other) <= Len(__longest)

-----------------------------------------------------------------------------

(**
 * Range(a % b) = 0..b-1, but DOMAIN seq = 1..Len(seq).
 * So to do modular arithmetic on sequences we need to map 0 to b.
 *
 * @type: (Int, Int) => Int;
 *)
SeqMod(__a, __b) == 
  IF __a % __b = 0 THEN __b ELSE __a % __b

(**
 * An alias of FoldFunction that op on all elements of seq an arbitrary
 * order. The resulting function is:
 *
 *    op(f[i],op(f[j], ..., op(f[k],base) ...))
 *
 * op must be associative and commutative, because we can not assume a
 * particular ordering of i, j, and k
 *
 * Example:
 *
 *  FoldSeq(LAMBDA x,y: {x} \cup y, {}, <<1,2,1>>) = Range(<<1,2,1>>)
 *
 * @type: ((a, b) => b, b, Seq(a)) => b;
 *)
FoldSeq(__op(_, _), __base, __seq) == 
  \* __ApalacheFoldSeq is accumulating the result in the left argument,
  \* whereas FoldSeq is accumulating the result in the right argument.
  LET __map(__y, __x) == __op(__x, __y) IN
  __ApalacheFoldSeq(__map, __base, __seq)

(**
 * FoldLeft folds op on all elements of seq from left to right, starting
 * with the first element and base. The resulting function is:
 *    op(op(...op(base,f[0]), ...f[n-1]), f[n])
 *
 * Example:
 *    LET cons(x,y) == <<x,y>>
 *    IN FoldLeft(cons, 0, <<3, 1, 2>>) = << << <<0, 3>>, 1>>, 2>> 
 *
 * @type: ((b, a) => b, b, Seq(a)) => b;
 *)
FoldLeft(__op(_, _), __base, __seq) == 
  LET __map(__x, __y) == __op(__x, __y) IN
  __ApalacheFoldSeq(__map, __base, __seq)

(**
 * FoldRight folds op on all elements of seq from right to left, starting
 * with the last element and base. The resulting function is:
 *    op(f[0],op(f[1], ..., op(f[n],base) ...))
 *
 *
 * Example:
 *    LET cons(x,y) == <<x,y>>
 *    IN FoldRight(cons, <<3, 1, 2>>, 0 ) = << 3, << 1, <<2, 0>> >> >> 
 *
 * @type: ((a, b) => b, Seq(a), b) => b;
 *)
FoldRight(__op(_, _), __seq, __base) == 
  LET __map(__y, __x) == __op(__x, __y) IN
  __ApalacheFoldSeq(__map, __base, Reverse(__seq))

-----------------------------------------------------------------------------

(**
 * A sequence of all elements from all sequences in the sequence seqs.
 *
 * Examples:
 *
 *  FlattenSeq(<< <<1, 2>>, <<1>> >>) = << 1, 2, 1 >>
 *  FlattenSeq(<< <<"a">>, <<"b">> >>) = <<"a", "b">>
 *
 * In contrast to TLC, Apalache treats strings as indivisible.
 * Hence, the following test of the community modules would not pass
 * (it is actually ill-typed):
 *
 *  FlattenSeq(<< "a", "b" >>) = "ab"
 *
 * @type: Seq(Seq(a)) => Seq(a);
 *)
FlattenSeq(__seqs) ==
  LET \* @type: (Seq(a), Seq(a)) => Seq(a);
      __concat(__s, __t) == __s \o __t
  IN
  __ApalacheFoldSeq(__concat, <<>>, __seqs)

(**
 * A sequence where the i-th tuple contains the i-th element of s and
 * t in this order.  Not defined for  Len(s) # Len(t)
 *
 * Examples:
 *
 *  Zip(<< >>, << >>) = << >>
 *  Zip(<<"a">>, <<"b">>) = << <<"a", "b">> >>
 *  Zip(<<1, 3>>, <<2, 4>>) = << <<1, 2>>, <<3, 4>> >>
 *  FlattenSeq(Zip(<<1, 3>>, <<2, 4>>)) = << <<1, 2>>, <<3, 4>> >>
 *
 * @type: (Seq(a), Seq(b)) => Seq(<<a, b>>);
 *)
Zip(__s, __t) ==
  LET \* @type: Int => <<a, b>>;
      __mk_tup(__i) == <<__s[__i], __t[__i]>>
  IN
  IF Len(__s) /= Len(__t)
  THEN \* the community modules do not specify the behavior for this case
    <<>>
  ELSE
    SubSeq(__ApalacheMkSeq(__ApalacheSeqCapacity(__s), __mk_tup), 1, Len(__s))

(**
 * The set of all subsequences of the sequence  s. Note that the empty
 * sequence  <<>>  is defined to be a subsequence of any sequence.
 *
 * @type: Seq(a) => Set(Seq(a));
 *)
SubSeqs(__s) ==
  { SubSeq(__s, __i + 1, __j): __i, __j \in {0} \union (DOMAIN __s) }

(**
 * The (1-based) index of the beginning of the subsequence haystack of the
 * sequence needle. If needle appears in haystack multiple times,
 * this equals the lowest index.
 *
 * Note that if needle does not belong to haystack, the result is undefined.
 *
 * For example:  IndexFirstSubSeq(<<1>>, <<1,1,1>>) = 1
 *
 * @type: (Seq(a), Seq(a)) => Int;
 *)
IndexFirstSubSeq(__needle, __haystack) ==
  LET __needle_len ==
    Len(__needle)
  IN
  LET __is_subseq(__i) ==
    __needle = SubSeq(__haystack, __i, __i + __needle_len - 1)
  IN
  LET __dom0 == {0} \union DOMAIN __haystack IN
  CHOOSE __i \in __dom0:
    /\ __is_subseq(__i)
    /\ \A __j \in __dom0:
          __j < __i => ~__is_subseq(__j)

(**
 * The sequence t with its subsequence s at position i replaced by
 * the sequence r.
 *
 * @type: (Int, Seq(a), Seq(a), Seq(a)) => Seq(a);
 *)
ReplaceSubSeqAt(__i, __r, __s, __t) ==
  LET __prefix == SubSeq(__t, 1, __i - 1)
      __suffix == SubSeq(__t, __i + Len(__s), Len(__t))
  IN
  __prefix \o __r \o __suffix 

(**
 * The sequence t with its subsequence s replaced by the sequence r.
 *
 * @type: (Seq(a), Seq(a), Seq(a)) => Seq(a);
 *)
ReplaceFirstSubSeq(__r, __s, __t) ==
  IF \*s \in SubSeqs(t)
    \E __i \in {0} \union DOMAIN __t:
      __s = SubSeq(__t, __i, __i + Len(__s))
  THEN ReplaceSubSeqAt(IndexFirstSubSeq(__s, __t), __r, __s, __t)
  ELSE __t

(**
 * The sequence  t  with all subsequences  s  replaced by the sequence  r
 * Overlapping replacements are disambiguated by choosing the occurrence
 * closer to the beginning of the sequence.
 *
 * Examples:
 *
 *  ReplaceAllSubSeqs(<<>>,<<>>,<<>>) = <<>>
 *  ReplaceAllSubSeqs(<<4>>,<<>>,<<>>) = <<4>>
 *  ReplaceAllSubSeqs(<<2>>,<<3>>,<<1,3>>) = <<1,2>>
 *  ReplaceAllSubSeqs(<<2,2>>,<<1,1>>,<<1,1,1>>) = <<2,2,1>>
 *)
ReplaceAllSubSeqs(__r, __s, __t) ==
  \* This operator has a massive definition,
  \* which we do not know how to translate.
  \* We skip it.
  \*
  \* https://github.com/tlaplus/CommunityModules/blob/48d8f59a9f530d93838c68c1b7070e83549420b9/modules/SequencesExt.tla#L344-L382
  __NotSupportedByModelChecker("ReplaceAllSubSeqs")
  
===============================================================================
