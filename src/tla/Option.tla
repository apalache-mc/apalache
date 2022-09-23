------------------- MODULE Option -----------------------
(**
 * Operators leveraging Apalache Variants to implement option types.
 *
 * Option types are a common algebraic data type used to represent values of a
 * partial computation. See https://en.wikipedia.org/wiki/Option_type
 *
 * Shon Feder, Informal Systems, 2022
 *)

EXTENDS Apalache, Variants

(* @typeAlias: option = Some(a) | None(UNIT); *)

(**
 * Lift a value of type `a` into an option.
 *
 * @param x a value
 * @return the variant representing a value in the domain
 *
 * @type: a => $option;
 *)
Some(__x) == Variant("Some", __x)

(**
 * The empty value.
 *
 * @return the variant representing an empty value, not in the domain
 *
 * @type: () => $option;
 *)
None == Variant("None", UNIT)

(**
 * `IsSome(o)` is `TRUE` iff `o = Some(v)` for a wrapped value `v`.
 *
 * @type: $option => Bool;
 *)
IsSome(__o) == VariantTag(__o) = "Some"

(**
 * `IsNone` is `TRUE` iff `o = None`.
 *
 * @type: $option => Bool;
 *)
IsNone(__o) == VariantTag(__o) = "None"

(**
 * `OptionCase(o, __caseSome(_), __caseNone(_))` is `__caseSome(v)` if `o = Some(v)`
 * or `__caseNone(UNIT)` if `o = None`.
 *
 * This eliminates an option type by case analysis on the two possible
 * alternatives of the variant.
 *
 * @type: (Some(a) | None(UNIT), a => b, UNIT => b) => b;
 *)
OptionCase(__o, __caseSome(_), __caseNone(_)) ==
  IF IsSome(__o)
  THEN __caseSome(VariantGetUnsafe("Some", __o))
  ELSE __caseNone(UNIT)

(**
 * `OptionMap(f, o)` is `Some(f(v))` if `o = Some(v)`, or else `None`.
 *
 * @type: (a => b, Some(a) | None(UNIT)) => Some(b) | None(UNIT);
 *)
OptionMap(__f(_), __o) ==
  LET
    __caseSome(__x) == Some(__f(__x))
  IN
  \* Annotation required to appease monomorphism watchdog
  LET \* @type: UNIT => $option;
    __caseNone(__u) == None
  IN
  OptionCase(__o, __caseSome, __caseNone)

(**
 * `OptionFlatMap(f, o)` is `f(v)` if `o = Some(v)` or else `None`.
 *
 * This operator can be used to sequence the application of partial functions.
 *
 * E.g.,
 *
 * ```
 * LET incr(n) == Some(n + 1) IN
 * LET fail(n) == None IN
 * LET q == OptionFlatMap(incr, Some(1)) IN
 * LET r == OptionFlatMap(incr, q) IN
 * LET s == OptionFlatMap(fail, r) IN
 * /\ r = Some(3)
 * /\ s = None
 * ```
 *
 * @type: (a => Some(b) | None(UNIT), Some(a) | None(UNIT)) => Some(b) | None(UNIT);
 *)
OptionFlatMap(__f(_), __o) ==
  LET
    __caseSome(__x) == __f(__x)
  IN
  \* Annotation required to appease monomorphism watchdog
  LET \* @type: UNIT => Some(b) | None(UNIT);
    __caseNone(__u) == None
  IN
  OptionCase(__o, __caseSome, __caseNone)

(**
 * `OptionGetOrElse(o, default)` is `v` if `o = Some(v)` or else `default`.
 *
 * @type: ($option, a) => a;
 *)
OptionGetOrElse(__o, __default) ==
  LET __caseSome(__x) == __x IN
  LET __caseNone(__u) == __default IN
  OptionCase(__o, __caseSome, __caseNone)

(**
 * `OptionToSeq(o)` is `<<v>>` iff `o = Some(v)`, or else `<<>>`.
 *
 * @type: (Some(a) | None(UNIT)) => Seq(a);
 *)
OptionToSeq(__o) ==
  LET \* @type: a => Seq(a);
    __caseSome(__x) == <<__x>>
  IN
  LET \* @type: UNIT => Seq(a);
    __caseNone(__u) == <<>>
  IN
  OptionCase(__o, __caseSome, __caseNone)

(**
 * `OptionToSet(o)` is `{v}` iff `o = Some(v)`, or else `{}`.
 *
 * @type: (Some(a) | None(UNIT)) => Set(a);
 *)
OptionToSet(__o) ==
  LET \* @type: a => Set(a);
    __caseSome(__x) == {__x}
  IN
  LET \* @type: UNIT => Set(a);
    __caseNone(__u) == {}
  IN
  OptionCase(__o, __caseSome, __caseNone)

(**
 * `OptionGuess(s)` is `None` if `s = {}`, otherwise it is `Some(x)`, where `x \in s`
 *
 * `x` is selected from `s` non-deterministically.
 *
 * @type: Set(a) => Some(a) | None(UNIT);
 *)
OptionGuess(__s) ==
  LET __getter(__oa, __b) == IF IsSome(__oa) THEN __oa ELSE Some(__b) IN
  ApaFoldSet(__getter, None, __s)

(**
 * `OptionFunApp(f, o)` is `Some(f[v])` if `o = Some(v)` or else `None`.
 *
 * @type: (a -> b, Some(a) | None(UNIT)) => Some(b) | None(UNIT);
 *)
OptionFunApp(__f, __o) ==
  LET __app(__x) == __f[__x] IN
  OptionMap(__app, __o)

(**
 * `OptionPartialFun(f, undef)` is a function mapping each value in `undef` to `None`,
 * and each value `x \in (DOMAIN f \ undef)` to `Some(f[x])`.
 *
 * This can be used to extend a total function a "partial function" whose domain is expanded
 * to include the vaules in 'undef'.
 *
 * @type: (a -> b, Set(a)) => (a -> Some(b) | None(UNIT));
 *)
OptionPartialFun(__f, __undefined) ==
  [__x \in DOMAIN __f \union __undefined |-> IF __x \in __undefined THEN None ELSE Some(__f[__x]) ]

============================================================
