------------------- MODULE Option -----------------------
EXTENDS Apalache, Variants

\* @typeAlias: option = Some(a) | None(UNIT);

\* @type: a => $option;
Some(x) == Variant("Some", x)
\* @type: () => $option;
None == Variant("None", UNIT)

\* @type: $option => Bool;
IsSome(o) == VariantTag(o) = "Some"
\* @type: $option => Bool;
IsNone(o) == VariantTag(o) = "None"

\* @type: (Some(a) | None(UNIT), a => b, UNIT => b) => b;
OptionCase(o, f(_), g(_)) ==
  IF IsSome(o)
  THEN f(VariantGetUnsafe("Some", o))
  ELSE g(UNIT)

\* @type: (a => b, Some(a) | None(UNIT)) => Some(b) | None(UNIT);
OptionMap(f(_), o) ==
  LET
    caseSome(x) == Some(f(x))
  IN
  \* Annotation required to appease monomorphism watchdog
  LET \* @type: UNIT => $option;
    caseNone(u) == None
  IN
  OptionCase(o, caseSome, caseNone)

\* @type: (a => Some(b) | None(UNIT), Some(a) | None(UNIT)) => Some(b) | None(UNIT);
OptionFlatMap(f(_), o) ==
  LET
    caseSome(x) == f(x)
  IN
  \* Annotation required to appease monomorphism watchdog
  LET \* @type: UNIT => Some(b) | None(UNIT);
    caseNone(u) == None
  IN
  OptionCase(o, caseSome, caseNone)

\* @type: ($option, a) => a;
OptionGetOrElse(o, default) ==
  LET caseSome(x) == x IN
  LET caseNone(u) == default IN
  OptionCase(o, caseSome, caseNone)

\* @type: (Some(a) | None(UNIT)) => Seq(a);
OptionToSeq(o) ==
  LET \* @type: a => Seq(a);
    caseSome(x) == <<x>>
  IN
  LET \* @type: UNIT => Seq(a);
    caseNone(u) == <<>>
  IN
  OptionCase(o, caseSome, caseNone)

\* @type: (Some(a) | None(UNIT)) => Set(a);
OptionToSet(o) ==
  LET \* @type: a => Set(a);
    caseSome(x) == {x}
  IN
  LET \* @type: UNIT => Set(a);
    caseNone(u) == {}
  IN
  OptionCase(o, caseSome, caseNone)

\* @type: Set(a) => Some(a) | None(UNIT);
OptionChoose(s) ==
  LET getter(oa, b) == IF IsSome(oa) THEN oa ELSE Some(b) IN
  ApaFoldSet(getter, None, s)

============================================================
