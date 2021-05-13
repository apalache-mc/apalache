package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.{BoolT1, _}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.DeepCopy
import at.forsyte.apalache.tla.pp.NormalizedNames
import TypedPredefs._
import com.typesafe.scalalogging.LazyLogging

import scala.annotation.tailrec
import scala.collection.immutable.SortedMap

/**
 * Generator of verification conditions. In the current implementation, VCGenerator takes an invariant candidate,
 * decomposes the invariant into smaller invariant candidates and produces negations of the invariant candidates.
 * In the future, we would temporal formulas as well.
 *
 * @author Igor Konnov
 */
class VCGenerator(tracker: TransformationTracker) extends LazyLogging {

  /**
   * Given a module and the name of an invariant candidate, add verification conditions in the module.
   *
   * @param module  an input module
   * @param invName the name of an invariant
   * @return a transformed module
   */
  def gen(module: TlaModule, invName: String): TlaModule = {
    val levelFinder = new TlaDeclLevelFinder(module)

    module.declarations.find(_.name == invName) match {
      case Some(inv: TlaOperDecl) if inv.formalParams.isEmpty =>
        // either a state invariant, or an action invariant
        val level = levelFinder(inv)
        level match {
          case TlaLevelConst | TlaLevelState | TlaLevelAction =>
            TlaModule(module.name, module.declarations ++ introConditions(level, inv.body))

          case TlaLevelTemporal =>
            val message = s"Expected a state invariant or an action invariant in $invName, found a temporal property"
            throw new MalformedTlaError(message, inv.body)
        }

      case Some(traceInv @ TlaOperDecl(name, params @ List(OperParam(_, 0)), body)) =>
        // a trace invariant
        if (TlaLevelConst != levelFinder(traceInv)) {
          throw new MalformedTlaError(
              s"Trace invariant $invName should not refer to state variables or use action/temporal operators", body)
        }
        assertTraceInvType(module, traceInv)
        val copy = DeepCopy(tracker)
        // we do not decompose trace invariants, so a trace invariant always has index 0
        val positive =
          TlaOperDecl(NormalizedNames.VC_TRACE_INV_PREFIX + "0", params, copy.deepCopyEx(body))(traceInv.typeTag)
        val notBody = tla.not(tla.fromTlaEx(copy.deepCopyEx(body))).typed(BoolT1())
        val negative =
          TlaOperDecl(NormalizedNames.VC_NOT_TRACE_INV_PREFIX + "0", params, notBody)(traceInv.typeTag)
        TlaModule(module.name, module.declarations :+ positive :+ negative)

      case Some(decl: TlaOperDecl) =>
        val nparams = decl.formalParams.length
        val message =
          s"Expected a state/action invariant $invName (0 parameters) or a trace invariant (1 parameter), found $nparams parameters"
        throw new MalformedTlaError(message, decl.body)

      case Some(decl) =>
        val message = s"Expected a nullary operator $invName, found ${decl.getClass.getSimpleName}"
        throw new MalformedTlaError(message, NullEx)

      case None =>
        throw new MalformedTlaError(s"Invariant candidate $invName not found", NullEx)
    }
  }

  private def assertTraceInvType(module: TlaModule, traceInv: TlaOperDecl): Unit = {
    val varTypes = SortedMap(module.varDeclarations.map(d => d.name -> d.typeTag.asTlaType1()): _*)
    // the history variable is a sequence of records over variable names
    val histType = SeqT1(RecT1(varTypes))
    if (traceInv.typeTag.asTlaType1() != OperT1(Seq(histType), BoolT1())) {
      val msg =
        s"Expected the trace invariant ${traceInv.name} to be a predicate of a sequence of records over the names of state variables"
      throw new MalformedTlaError(msg, traceInv.body)
    }
  }

  private def introConditions(level: TlaLevel, inputInv: TlaEx): Seq[TlaOperDecl] = {
    def mapToDecls(invPiece: TlaEx, index: Int): Seq[TlaOperDecl] = {
      val deepCopy = DeepCopy(tracker)
      val invPieceCopy = deepCopy.deepCopyEx(invPiece)
      val tag = inputInv.typeTag
      val positivePrefix =
        if (level == TlaLevelAction) NormalizedNames.VC_ACTION_INV_PREFIX else NormalizedNames.VC_INV_PREFIX
      val positive = TlaOperDecl(positivePrefix + index, List(), invPieceCopy)(tag)
      val notInvPieceCopy = tla.not(invPieceCopy).typed(BoolT1())
      val negativePrefix =
        if (level == TlaLevelAction) NormalizedNames.VC_NOT_ACTION_INV_PREFIX else NormalizedNames.VC_NOT_INV_PREFIX
      val negative = TlaOperDecl(negativePrefix + index, List(), notInvPieceCopy)(tag)
      Seq(positive, negative)
    }

    val fragments = splitInv(Seq(), inputInv)
    logger.info(s"  > VCGen produced ${fragments.length} verification condition(s)")
    fragments.zipWithIndex.flatMap { case (e, i) => mapToDecls(e, i) }
  }

  private def splitInv(universalsRev: Seq[(NameEx, TlaEx)], inv: TlaEx): Seq[TlaEx] = {
    inv match {
      case OperEx(TlaBoolOper.forall, nameEx @ NameEx(_), set, pred) =>
        // \A x \in S: B /\ C is equivalent to (\A x \in S: B) /\ (\A x \in S: C)
        splitInv((nameEx, set) +: universalsRev, pred)

      case OperEx(TlaBoolOper.and, args @ _*) =>
        // we split A /\ B into the set {A, B}
        args.flatMap(splitInv(universalsRev, _))

      case _ =>
        // nothing to split, just add quantifiers that were collected on the way
        Seq(decorateWithUniversals(universalsRev, inv))
    }
  }

  @tailrec
  private def decorateWithUniversals(universalsRev: Seq[(NameEx, TlaEx)], expr: TlaEx): TlaEx = {
    universalsRev match {
      case Nil =>
        expr

      case (nameEx, set) :: tail =>
        decorateWithUniversals(tail, tla.forall(nameEx, set, expr).typed(BoolT1()))
    }
  }
}
