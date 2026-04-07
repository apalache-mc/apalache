package at.forsyte.apalache.tla.typecheck.etcfast

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecheck._
import at.forsyte.apalache.tla.typecheck.etc.EtcTypeChecker
import at.forsyte.apalache.tla.typecheck.etc.{EtcAbs, EtcApp, EtcAppByName, EtcBuilder, EtcConst, EtcExpr, EtcLet, EtcName, EtcRef, EtcTypeDecl, ExactRef}
import at.forsyte.apalache.tla.types.TypeUnifier
import at.forsyte.apalache.tla.types.TypeVarPool

import scala.collection.immutable.SortedMap
import scala.collection.mutable

class EtcTypeCheckerFast(varPool: TypeVarPool, inferPolytypes: Boolean = true) extends TypeChecker with EtcBuilder {
  import EtcTypeCheckerFast._

  private var listener: TypeCheckerListener = new DefaultTypeCheckerListener()
  private val globalVars = new mutable.HashMap[Int, TVar]()

  override def compute(typeListener: TypeCheckerListener, rootCtx: TypeContext, rootEx: EtcExpr): Option[TlaType1] = {
    listener = typeListener
    globalVars.clear()
    try {
      val rootType = infer(initialEnv(rootCtx), level = 0, rootEx, expected = None)
      val exactType = export(rootType)
      onTypeFound(rootEx.sourceRef, exactType)
      Some(exactType)
    } catch {
      case _: NeedLegacyFallback =>
        val legacyVarPool = new TypeVarPool(varPool.size)
        new EtcTypeChecker(legacyVarPool, inferPolytypes).compute(typeListener, rootCtx, rootEx)

      case _: UnwindException => None
    }
  }

  private def initialEnv(ctx: TypeContext): FastEnv = {
    val types = ctx.types.map { case (name, scheme) => name -> fromExternalScheme(scheme, shareUnquantified = true) }
    new FastEnv(types)
  }

  private def infer(env: FastEnv, level: Int, ex: EtcExpr, expected: Option[FType]): FType = {
    ex match {
      case EtcConst(polytype) =>
        fromExternalType(polytype, shareUnquantified = true)

      case EtcTypeDecl(name, declaredType, scopedEx) =>
        val quantified = declaredType.usedNames
        val declaredScheme = fromExternalScheme(TlaType1Scheme(declaredType, quantified), shareUnquantified = true)
        if (quantified.isEmpty) {
          onTypeFound(ex.sourceRef, declaredType)
        }
        infer(env.withBinding(name, declaredScheme), level, scopedEx, expected)

      case EtcName(name) =>
        env.types.get(name) match {
          case Some(scheme) =>
            val inferred = instantiate(scheme, level)
            onTypeFound(ex.sourceRef, export(inferred))
            inferred

          case None =>
            onTypeError(ex.sourceRef, s"No annotation found for $name. Make sure that you've put one in front of $name.")
            throw new UnwindException
        }

      case appEx @ EtcApp(operTypes, args @ _*) =>
        inferApp(env, level, appEx, operTypes, args.toList, expected, None)

      case appEx @ EtcAppByName(name, args @ _*) =>
        env.types.get(name.name) match {
          case Some(scheme) =>
            val instantiatedType = instantiate(scheme, level)
            onTypeFound(name.sourceRef, export(instantiatedType))
            inferApp(env, level, appEx, Seq(export(instantiatedType)), args.toList, expected, Some(name.sourceRef))

          case None =>
            onTypeError(ex.sourceRef, s"The operator $name is used before it is defined.")
            throw new UnwindException
        }

      case EtcAbs(scopedEx, binders @ _*) =>
        val (extEnv, paramTypes) = translateBinders(env, level, binders.toList)
        val bodyType = infer(extEnv, level, scopedEx, expected.collect { case FOper(_, res) => res })
        val operType = FOper(paramTypes, bodyType)
        onTypeFound(ex.sourceRef, export(operType))
        operType

      case letEx @ EtcLet(name, defEx @ EtcAbs(defBody, binders @ _*), scopedEx) =>
        val operScheme = annotationToOperScheme(env, level, name, binders.length)
        val preEnv = env.withBinding(name, operScheme)
        val (extEnv, paramTypes) = translateBinders(preEnv, level + 1, binders.toList)
        val expectedRes = operScheme.principal match {
          case FOper(_, res) => Some(res)
          case _             => None
        }
        operScheme.principal match {
          case FOper(annotationParams, _) =>
            annotationParams.zip(paramTypes).zip(binders).foreach { case ((annotParam, paramType), (pname, _)) =>
              try {
                unify(paramType, annotParam)
              } catch {
                case _: TypeMismatchException =>
                  onTypeError(defEx.sourceRef, s"Mismatch in parameter ${pname.name}. Found: ${export(paramType)}")
                  throw new UnwindException
              }
            }

          case other =>
            throw new IllegalStateException("Expected an operator type, found: " + export(other))
        }

        val defBodyType = infer(extEnv, level + 1, defBody, expectedRes)
        val defType = FOper(paramTypes, defBodyType)
        try {
          unify(operScheme.principal, defType)
        } catch {
          case _: TypeMismatchException =>
            val expected = export(operScheme.principal)
            val found = export(defType)
            onTypeError(defEx.sourceRef, s"Expected $expected in $name. Found: $found")
            throw new UnwindException
        }

        val principalDefType = export(defType)
        val generalized = generalize(level, defType)
        if (!inferPolytypes && generalized.quantified.nonEmpty) {
          onTypeError(ex.sourceRef,
              s"Operator $name has a parameterized type, while polymorphism is disabled: " + principalDefType)
          throw new UnwindException
        }

        env.types.get(name).foreach { userScheme =>
          val inferredType = principalDefType
          val userType = export(userScheme.principal) match {
            case op: OperT1 => op
            case someType   => OperT1(Seq(), someType)
          }
          new TypeUnifier(varPool).unify(at.forsyte.apalache.tla.types.Substitution.empty, inferredType, userType) match {
            case None =>
              val msg = s"Contradiction in the type solver: $inferredType and $userType should be unifiable"
              throw new TypingException(msg, letEx.sourceRef.tlaId)

            case Some((_, unifiedType)) =>
              if (unifiedType.usedNames.size < userType.usedNames.size) {
                onTypeWarn(letEx.sourceRef, s"$name's type annotation $userType is too general, inferred: $inferredType")
              }
          }
        }

        onTypeFound(defEx.sourceRef, principalDefType)
        infer(env.withBinding(name, generalized), level, scopedEx, expected)

      case EtcLet(_, _, _) =>
        throw new RuntimeException("Bug in type checker. Ill-formed let-expression: " + ex)
    }
  }

  private def inferApp(
      env: FastEnv,
      level: Int,
      appEx: EtcExpr,
      operTypes: Seq[TlaType1],
      args: List[EtcExpr],
      expected: Option[FType],
      operatorNameRef: Option[EtcRef]): FType = {
    val argTypes = args.map(infer(env, level, _, None))
    val resType = freshVar(level)
    val appliedOperType = FOper(argTypes, resType)
    expected.foreach(unify(resType, _))

    def evaluatedArgTypes: List[TlaType1] = argTypes.map(export)

    def onArgsMatchError(sig: TlaType1): Nothing = {
      val argOrArgs = pluralArgs(argTypes.length)
      val defaultMessage =
        s"An operator with the signature $sig cannot be applied to the provided $argOrArgs of type ${evaluatedArgTypes.mkString(" and ")}"
      val specificMessage = appEx.explain(List(sig), evaluatedArgTypes)
      onTypeError(appEx.sourceRef, specificMessage.getOrElse(defaultMessage))
      throw new UnwindException
    }

      if (operTypes.length == 1) {
      val operType = fromExternalType(operTypes.head, shareUnquantified = true)
      try {
        unify(operType, appliedOperType)
      } catch {
        case _: TypeMismatchException =>
          onArgsMatchError(export(operType))
      }
      args.zip(argTypes).foreach { case (arg, argType) => onTypeFound(arg.sourceRef, export(argType)) }
      operatorNameRef.foreach(ref => onTypeFound(ref, export(operType)))
      val exactResult = export(resType)
      onTypeFound(appEx.sourceRef, exactResult)
      resType
    } else {
      val successful = operTypes.flatMap { sig =>
        val checkpoint = snapshot()
        val localSig = fromExternalType(sig, shareUnquantified = false)
        val localRes = freshVar(level)
        val localApplied = FOper(argTypes.map(cloneType(_, mutable.HashMap.empty, preserveShared = true)), localRes)
        val option =
          try {
            expected.foreach(exp => unify(localRes, cloneType(exp, mutable.HashMap.empty, preserveShared = true)))
            unify(localSig, localApplied)
            Some((sig, export(localSig), export(localRes)))
          } catch {
            case _: TypeMismatchException => None
          }
        rollback(checkpoint)
        option
      }

      successful match {
        case Seq((sig, _, _)) =>
          val operType = fromExternalType(sig, shareUnquantified = true)
          try {
            unify(operType, appliedOperType)
          } catch {
            case _: TypeMismatchException =>
              onArgsMatchError(export(operType))
          }
          args.zip(argTypes).foreach { case (arg, argType) => onTypeFound(arg.sourceRef, export(argType)) }
          operatorNameRef.foreach(ref => onTypeFound(ref, export(operType)))
          val exactResult = export(resType)
          onTypeFound(appEx.sourceRef, exactResult)
          resType

        case Seq() =>
          val argOrArgs = pluralArgs(argTypes.length)
          onTypeError(appEx.sourceRef, s"No matching signature for $argOrArgs ${evaluatedArgTypes}")
          throw new UnwindException

        case many =>
          throw new NeedLegacyFallback
      }
    }
  }

  private def annotationToOperScheme(env: FastEnv, level: Int, name: String, arity: Int): FastScheme = {
    env.types.get(name) match {
      case Some(scheme) =>
        prune(scheme.principal) match {
          case op: FOper => instantiateSchemeAsMonotype(scheme, level, expectedArity = Some(op.args.length))
          case other     => FastScheme(FOper(Seq.empty, other), scheme.quantified)
        }

      case None =>
        val args = 1.to(arity).map(_ => freshVar(level + 1))
        val res = freshVar(level + 1)
        FastScheme(FOper(args, res), (args.map(_.id) :+ res.id).toSet)
    }
  }

  private def instantiateSchemeAsMonotype(scheme: FastScheme, level: Int, expectedArity: Option[Int] = None): FastScheme = {
    val principal = instantiate(scheme, level)
    principal match {
      case op: FOper =>
        expectedArity.foreach { arity =>
          if (op.args.length != arity) {
            throw new IllegalStateException(s"Expected arity $arity, found ${op.args.length}")
          }
        }
        FastScheme(op, Set.empty)

      case other =>
        FastScheme(other, Set.empty)
    }
  }

  private def translateBinders(env: FastEnv, level: Int, binders: List[(EtcName, EtcExpr)]): (FastEnv, Seq[FType]) = {
      val setTypes = binders.map { case (_, setEx) => infer(env, level, setEx, None) }
    val elemVars = binders.map(_ => freshVar(level))
    binders.zip(setTypes.zip(elemVars)).foreach { case ((_, setEx), (setType, elemType)) =>
      try {
        unify(setType, FSet(elemType))
      } catch {
        case _: TypeMismatchException =>
          onTypeError(setEx.sourceRef, "Expected a set. Found: " + export(setType))
          throw new UnwindException
      }
      onTypeFound(setEx.sourceRef, export(FSet(elemType)))
    }
    binders.zip(elemVars).foreach { case ((name, _), elemType) =>
      onTypeFound(name.sourceRef, export(elemType))
    }
    val binderSchemes = binders.map(_._1.name).zip(elemVars.map(FastScheme(_, Set.empty)))
    (env.withBindings(binderSchemes), elemVars)
  }

  private def generalize(level: Int, tp: FType): FastScheme = {
    val quantified = mutable.Set[Int]()
    collectGeneralizable(prune(tp), level, quantified, mutable.Set.empty)
    FastScheme(prune(tp), quantified.toSet)
  }

  private def collectGeneralizable(
      tp: FType,
      level: Int,
      out: mutable.Set[Int],
      seen: mutable.Set[Int]): Unit = {
    prune(tp) match {
      case v: TVar =>
        if (!seen.contains(v.id)) {
          seen += v.id
          if (v.link.isEmpty && v.level > level) {
            out += v.id
          } else {
            v.link.foreach(collectGeneralizable(_, level, out, seen))
          }
        }

      case FSet(elem) =>
        collectGeneralizable(elem, level, out, seen)

      case FSeq(elem) =>
        collectGeneralizable(elem, level, out, seen)

      case FFun(arg, res) =>
        collectGeneralizable(arg, level, out, seen)
        collectGeneralizable(res, level, out, seen)

      case FOper(args, res) =>
        args.foreach(collectGeneralizable(_, level, out, seen))
        collectGeneralizable(res, level, out, seen)

      case FTup(elems) =>
        elems.foreach(collectGeneralizable(_, level, out, seen))

      case FSparseTup(fields) =>
        fields.values.foreach(collectGeneralizable(_, level, out, seen))

      case FRec(fields) =>
        fields.values.foreach(collectGeneralizable(_, level, out, seen))

      case FRow(fields, tail) =>
        fields.values.foreach(collectGeneralizable(_, level, out, seen))
        tail.foreach(collectGeneralizable(_, level, out, seen))

      case FRecRow(row) =>
        collectGeneralizable(row, level, out, seen)

      case FVariant(row) =>
        collectGeneralizable(row, level, out, seen)

      case _ =>
    }
  }

  private def instantiate(scheme: FastScheme, level: Int): FType = {
    cloneType(scheme.principal, mutable.HashMap.empty, preserveShared = false, quantified = scheme.quantified, level = level)
  }

  private def fromExternalScheme(scheme: TlaType1Scheme, shareUnquantified: Boolean): FastScheme = {
    FastScheme(fromExternalType(scheme.principalType, shareUnquantified), scheme.quantifiedVars)
  }

  private def fromExternalType(tt: TlaType1, shareUnquantified: Boolean): FType = {
    def convert(tp: TlaType1, cache: mutable.HashMap[Int, TVar]): FType = {
      tp match {
        case IntT1      => FInt
        case BoolT1     => FBool
        case RealT1     => FReal
        case StrT1      => FStr
        case c: ConstT1 => FConst(c.name)
        case VarT1(no) =>
          if (shareUnquantified) {
            globalVars.getOrElseUpdate(no, TVar(no, 0))
          } else {
            cache.getOrElseUpdate(no, TVar(no, 0))
          }
        case SetT1(elem) =>
          FSet(convert(elem, cache))
        case SeqT1(elem) =>
          FSeq(convert(elem, cache))
        case FunT1(arg, res) =>
          FFun(convert(arg, cache), convert(res, cache))
        case OperT1(args, res) =>
          FOper(args.map(convert(_, cache)), convert(res, cache))
        case TupT1(elems @ _*) =>
          FTup(elems.map(convert(_, cache)))
        case SparseTupT1(fields) =>
          FSparseTup(SortedMap(fields.toSeq.map { case (k, v) => k -> convert(v, cache) }: _*))
        case RecT1(fields) =>
          FRec(SortedMap(fields.toSeq.map { case (k, v) => k -> convert(v, cache) }: _*))
        case RowT1(fields, tail) =>
          FRow(SortedMap(fields.toSeq.map { case (k, v) => k -> convert(v, cache) }: _*),
              tail.map(v => convert(v, cache).asInstanceOf[TVar]))
        case RecRowT1(row) =>
          FRecRow(convert(row, cache).asInstanceOf[FRow])
        case VariantT1(row) =>
          FVariant(convert(row, cache).asInstanceOf[FRow])
      }
    }

    convert(tt, mutable.HashMap.empty)
  }

  private def export(tp: FType): TlaType1 = {
    val cache = mutable.HashMap[Int, TlaType1]()

    def loop(term: FType): TlaType1 = {
      prune(term) match {
        case v: TVar =>
          cache.getOrElseUpdate(v.id, {
            v.link match {
              case Some(target) => loop(target)
              case None         => VarT1(v.id)
            }
          })
        case FInt         => IntT1
        case FBool        => BoolT1
        case FReal        => RealT1
        case FStr         => StrT1
        case FConst(name) => ConstT1(name)
        case FSet(elem)   => SetT1(loop(elem))
        case FSeq(elem)   => SeqT1(loop(elem))
        case FFun(arg, res) =>
          FunT1(loop(arg), loop(res))
        case FOper(args, res) =>
          OperT1(args.map(loop), loop(res))
        case FTup(elems) =>
          TupT1(elems.map(loop): _*)
        case FSparseTup(fields) =>
          SparseTupT1(SortedMap(fields.toSeq.map { case (k, v) => k -> loop(v) }: _*))
        case FRec(fields) =>
          RecT1(SortedMap(fields.toSeq.map { case (k, v) => k -> loop(v) }: _*))
        case FRow(fields, tail) =>
          RowT1(SortedMap(fields.toSeq.map { case (k, v) => k -> loop(v) }: _*),
              tail.map(v => loop(v).asInstanceOf[VarT1]))
        case FRecRow(row) =>
          RecRowT1(loop(row).asInstanceOf[RowT1])
        case FVariant(row) =>
          VariantT1(loop(row).asInstanceOf[RowT1])
      }
    }

    loop(tp)
  }

  private def freshVar(level: Int): TVar = {
    val id = varPool.fresh.no
    val variable = TVar(id, level)
    globalVars.getOrElseUpdate(id, variable)
    variable
  }

  private def prune(tp: FType): FType = {
    tp match {
      case v: TVar =>
        v.link match {
          case Some(next) =>
            val pruned = prune(next)
            v.link = Some(pruned)
            pruned
          case None => v
        }
      case _ =>
        tp
    }
  }

  private def snapshot(): Map[Int, Option[FType]] = {
    globalVars.iterator.map { case (id, tv) => id -> tv.link }.toMap
  }

  private def rollback(snapshot: Map[Int, Option[FType]]): Unit = {
    globalVars.foreach { case (id, tv) =>
      tv.link = snapshot.getOrElse(id, tv.link)
    }
  }

  private def unify(left: FType, right: FType): Unit = {
    (prune(left), prune(right)) match {
      case (l: TVar, r: TVar) if l.id == r.id =>
      case (l: TVar, other) =>
        bindVar(l, other)
      case (other, r: TVar) =>
        bindVar(r, other)
      case (FInt, FInt) | (FBool, FBool) | (FReal, FReal) | (FStr, FStr) =>
      case (FConst(l), FConst(r)) if l == r =>
      case (FSet(le), FSet(re)) =>
        unify(le, re)
      case (FSeq(le), FSeq(re)) =>
        unify(le, re)
      case (FFun(la, lr), FFun(ra, rr)) =>
        unify(la, ra)
        unify(lr, rr)
      case (FOper(largs, lres), FOper(rargs, rres)) if largs.length == rargs.length =>
        largs.zip(rargs).foreach { case (l, r) => unify(l, r) }
        unify(lres, rres)
      case (FTup(lelems), FTup(relems)) if lelems.length == relems.length =>
        lelems.zip(relems).foreach { case (l, r) => unify(l, r) }
      case (FSparseTup(lfields), FSparseTup(rfields)) =>
        val jointKeys = lfields.keySet ++ rfields.keySet
        jointKeys.foreach {
          case key if lfields.contains(key) && rfields.contains(key) => unify(lfields(key), rfields(key))
          case _ =>
        }
      case (l @ FSparseTup(_), FTup(relems)) =>
        val total = FSparseTup(SortedMap(relems.zipWithIndex.map { case (t, i) => (i + 1) -> t }: _*))
        unify(l, total)
      case (FTup(_), r @ FSparseTup(_)) =>
        unify(r, left)
      case (FRec(lfields), FRec(rfields)) =>
        val jointKeys = lfields.keySet ++ rfields.keySet
        jointKeys.foreach {
          case key if lfields.contains(key) && rfields.contains(key) => unify(lfields(key), rfields(key))
          case _ =>
        }
      case (FRow(lfields, ltail), FRow(rfields, rtail)) =>
        unifyRows(lfields, rfields, ltail, rtail)
      case (FRecRow(lrow), FRecRow(rrow)) =>
        unify(lrow, rrow)
      case (rec @ FRec(_), rowRec @ FRecRow(_)) =>
        unify(rowRec, rec)
      case (rowRec @ FRecRow(_), FRec(fields)) =>
        unify(rowRec, FRecRow(FRow(fields, None)))
      case (FVariant(lrow), FVariant(rrow)) =>
        unify(lrow, rrow)
      case _ =>
        throw new TypeMismatchException
    }
  }

  private def bindVar(variable: TVar, other: FType): Unit = {
    val prunedOther = prune(other)
    prunedOther match {
      case otherVar: TVar if otherVar.id == variable.id =>
      case otherVar: TVar if otherVar.link.isEmpty && variable.link.isEmpty =>
        val (winner, loser) = if (variable.id < otherVar.id) (variable, otherVar) else (otherVar, variable)
        winner.level = math.min(winner.level, loser.level)
        loser.link = Some(winner)
      case _ =>
        if (occurs(variable, prunedOther, mutable.Set.empty)) {
          throw new TypeMismatchException
        }
        lowerLevels(prunedOther, variable.level, mutable.Set.empty)
        variable.link = Some(prunedOther)
    }
  }

  private def occurs(variable: TVar, tp: FType, seen: mutable.Set[Int]): Boolean = {
    prune(tp) match {
      case v: TVar =>
        if (v.id == variable.id) true
        else if (seen.contains(v.id)) false
        else {
          seen += v.id
          v.link.exists(occurs(variable, _, seen))
        }
      case FSet(elem) =>
        occurs(variable, elem, seen)
      case FSeq(elem) =>
        occurs(variable, elem, seen)
      case FFun(arg, res) =>
        occurs(variable, arg, seen) || occurs(variable, res, seen)
      case FOper(args, res) =>
        args.exists(occurs(variable, _, seen)) || occurs(variable, res, seen)
      case FTup(elems) =>
        elems.exists(occurs(variable, _, seen))
      case FSparseTup(fields) =>
        fields.values.exists(occurs(variable, _, seen))
      case FRec(fields) =>
        fields.values.exists(occurs(variable, _, seen))
      case FRow(fields, tail) =>
        fields.values.exists(occurs(variable, _, seen)) || tail.exists(occurs(variable, _, seen))
      case FRecRow(row) =>
        occurs(variable, row, seen)
      case FVariant(row) =>
        occurs(variable, row, seen)
      case _ =>
        false
    }
  }

  private def lowerLevels(tp: FType, maxLevel: Int, seen: mutable.Set[Int]): Unit = {
    prune(tp) match {
      case v: TVar =>
        if (!seen.contains(v.id)) {
          seen += v.id
          if (v.link.isEmpty) {
            v.level = math.min(v.level, maxLevel)
          } else {
            v.link.foreach(lowerLevels(_, maxLevel, seen))
          }
        }
      case FSet(elem) =>
        lowerLevels(elem, maxLevel, seen)
      case FSeq(elem) =>
        lowerLevels(elem, maxLevel, seen)
      case FFun(arg, res) =>
        lowerLevels(arg, maxLevel, seen)
        lowerLevels(res, maxLevel, seen)
      case FOper(args, res) =>
        args.foreach(lowerLevels(_, maxLevel, seen))
        lowerLevels(res, maxLevel, seen)
      case FTup(elems) =>
        elems.foreach(lowerLevels(_, maxLevel, seen))
      case FSparseTup(fields) =>
        fields.values.foreach(lowerLevels(_, maxLevel, seen))
      case FRec(fields) =>
        fields.values.foreach(lowerLevels(_, maxLevel, seen))
      case FRow(fields, tail) =>
        fields.values.foreach(lowerLevels(_, maxLevel, seen))
        tail.foreach(lowerLevels(_, maxLevel, seen))
      case FRecRow(row) =>
        lowerLevels(row, maxLevel, seen)
      case FVariant(row) =>
        lowerLevels(row, maxLevel, seen)
      case _ =>
    }
  }

  private def unifyRows(
      lfields: SortedMap[String, FType],
      rfields: SortedMap[String, FType],
      ltail: Option[TVar],
      rtail: Option[TVar]): Unit = {
    if (lfields.isEmpty) {
      (ltail, rtail) match {
        case (None, None) =>
          if (rfields.nonEmpty) {
            throw new TypeMismatchException
          }
        case (Some(lv), Some(rv)) =>
          if (rfields.isEmpty) {
            unify(lv, rv)
          } else {
            bindVar(lv, FRow(rfields, rtail))
          }
        case (Some(lv), None) =>
          bindVar(lv, FRow(rfields, None))
        case (None, Some(rv)) =>
          if (rfields.isEmpty) bindVar(rv, FRow(SortedMap.empty, None))
          else throw new TypeMismatchException
      }
    } else if (rfields.isEmpty) {
      unifyRows(rfields, lfields, rtail, ltail)
    } else {
      val shared = lfields.keySet.intersect(rfields.keySet)
      if (shared.isEmpty) {
        val tailVar = freshVar(0)
        unify(ltail.getOrElse(FRow(SortedMap.empty, None)), FRow(rfields, Some(tailVar)))
        unify(rtail.getOrElse(FRow(SortedMap.empty, None)), FRow(lfields, Some(tailVar)))
      } else {
        val luniq = lfields.filterNot(p => shared.contains(p._1))
        val runiq = rfields.filterNot(p => shared.contains(p._1))
        unify(FRow(luniq, ltail), FRow(runiq, rtail))
        shared.foreach(key => unify(lfields(key), rfields(key)))
      }
    }
  }

  private def cloneType(
      tp: FType,
      cache: mutable.HashMap[Int, TVar],
      preserveShared: Boolean,
      quantified: Set[Int] = Set.empty,
      level: Int = 0): FType = {
    prune(tp) match {
      case v: TVar =>
        if (preserveShared && quantified.isEmpty) {
          v
        } else if (quantified.contains(v.id)) {
          cache.getOrElseUpdate(v.id, freshVar(level))
        } else {
          v.link match {
            case Some(target) => cloneType(target, cache, preserveShared, quantified, level)
            case None         => v
          }
        }
      case FSet(elem) =>
        FSet(cloneType(elem, cache, preserveShared, quantified, level))
      case FSeq(elem) =>
        FSeq(cloneType(elem, cache, preserveShared, quantified, level))
      case FFun(arg, res) =>
        FFun(cloneType(arg, cache, preserveShared, quantified, level),
            cloneType(res, cache, preserveShared, quantified, level))
      case FOper(args, res) =>
        FOper(args.map(cloneType(_, cache, preserveShared, quantified, level)),
            cloneType(res, cache, preserveShared, quantified, level))
      case FTup(elems) =>
        FTup(elems.map(cloneType(_, cache, preserveShared, quantified, level)))
      case FSparseTup(fields) =>
        FSparseTup(SortedMap(fields.toSeq.map { case (k, v) => k -> cloneType(v, cache, preserveShared, quantified, level) }: _*))
      case FRec(fields) =>
        FRec(SortedMap(fields.toSeq.map { case (k, v) => k -> cloneType(v, cache, preserveShared, quantified, level) }: _*))
      case FRow(fields, tail) =>
        FRow(SortedMap(fields.toSeq.map { case (k, v) => k -> cloneType(v, cache, preserveShared, quantified, level) }: _*),
            tail.map(v => cloneType(v, cache, preserveShared, quantified, level).asInstanceOf[TVar]))
      case FRecRow(row) =>
        FRecRow(cloneType(row, cache, preserveShared, quantified, level).asInstanceOf[FRow])
      case FVariant(row) =>
        FVariant(cloneType(row, cache, preserveShared, quantified, level).asInstanceOf[FRow])
      case other =>
        other
    }
  }

  private def onTypeFound(sourceRef: EtcRef, tt: TlaType1): Unit = {
    sourceRef match {
      case ref: ExactRef =>
        listener.onTypeFound(ref, tt)
      case _ =>
    }
  }

  private def onTypeError(sourceRef: EtcRef, message: String): Unit = {
    listener.onTypeError(sourceRef, message)
  }

  private def onTypeWarn(sourceRef: EtcRef, message: String): Unit = {
    listener.onTypeWarn(sourceRef, message)
  }

  private def pluralArgs(count: Int): String = if (count != 1) "arguments" else "argument"
}

object EtcTypeCheckerFast {
  private sealed trait FType
  private case object FInt extends FType
  private case object FBool extends FType
  private case object FReal extends FType
  private case object FStr extends FType
  private case class FConst(name: String) extends FType
  private case class TVar(id: Int, var level: Int, var link: Option[FType] = None) extends FType
  private case class FSet(elem: FType) extends FType
  private case class FSeq(elem: FType) extends FType
  private case class FFun(arg: FType, res: FType) extends FType
  private case class FOper(args: Seq[FType], res: FType) extends FType
  private case class FTup(elems: Seq[FType]) extends FType
  private case class FSparseTup(fields: SortedMap[Int, FType]) extends FType
  private case class FRec(fields: SortedMap[String, FType]) extends FType
  private case class FRow(fields: SortedMap[String, FType], tail: Option[TVar]) extends FType
  private case class FRecRow(row: FRow) extends FType
  private case class FVariant(row: FRow) extends FType

  private case class FastScheme(principal: FType, quantified: Set[Int])
  private class FastEnv(val types: Map[String, FastScheme]) {
    def withBinding(name: String, scheme: FastScheme): FastEnv =
      new FastEnv(types + (name -> scheme))

    def withBindings(bindings: Seq[(String, FastScheme)]): FastEnv =
      new FastEnv(types ++ bindings)
  }

  private class TypeMismatchException extends RuntimeException
  private class NeedLegacyFallback extends RuntimeException
  protected class UnwindException extends RuntimeException
}
