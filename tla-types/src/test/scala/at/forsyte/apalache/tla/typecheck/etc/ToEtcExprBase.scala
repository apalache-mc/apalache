package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.{OperT1, SetT1, TlaType1, TupT1, UID, VarT1}

/**
 * The base class to be used by TestToEtcExprFoo classes.
 */
protected trait ToEtcExprBase extends EtcBuilder {
  protected def mkToEtcExpr(
      annotations: Map[UID, TlaType1] = Map.empty,
      aliases: TypeAliasSubstitution = TypeAliasSubstitution.empty,
      useRows: Boolean = false): ToEtcExpr = {
    new ToEtcExpr(annotations, aliases, new TypeVarPool(), useRows)
  }

  protected def mkAppByType(operTypes: Seq[TlaType1], args: TlaType1*): EtcApp = {
    mkUniqApp(operTypes, args.map(a => mkUniqConst(a)): _*)
  }

  protected def mkAppByName(operTypes: Seq[TlaType1], args: String*): EtcApp = {
    mkUniqApp(operTypes, args.map(mkUniqName): _*)
  }

  protected def mkConstAppByType(opsig: TlaType1, args: TlaType1*): EtcApp = {
    mkUniqApp(Seq(opsig), args.map(a => mkUniqConst(a)): _*)
  }

  protected def mkConstAppByName(opsig: TlaType1, args: String*): EtcApp = {
    mkUniqApp(Seq(opsig), args.map(mkUniqName): _*)
  }

  // produce an expression that projects a set of pairs on the set of its first (or second) components
  protected def mkProjection(
      fst: String,
      snd: String,
      projFirst: Boolean,
      set: String): EtcExpr = {
    val axis = if (projFirst) fst else snd
    val tuple = TupT1(VarT1(fst), VarT1(snd))
    // Projection: depending on axis, either ((<<a, b>>, Set(<<a, b>>)) => Set(a)) or ((<<a, b>>, Set(<<a, b>>)) => Set(b))
    // We add the tuple <<a, b>> for technical reasons, in order to recover the type of the variable tuple in TypeRewriter.
    val oper = OperT1(Seq(tuple, SetT1(tuple)), SetT1(VarT1(axis)))
    mkUniqApp(Seq(oper), mkUniqConst(tuple), mkUniqName(set))
  }
}
