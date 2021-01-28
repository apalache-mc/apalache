package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.DeepCopy
import at.forsyte.apalache.tla.pp.NormalizedNames
import com.typesafe.scalalogging.LazyLogging

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
    * @param module an input module
    * @param invName the name of an invariant
    * @return a transformed module
    */
  def gen(module: TlaModule, invName: String): TlaModule = {
    module.declarations.find(_.name == invName) match {
      case Some(inv: TlaOperDecl) if inv.formalParams.isEmpty =>
        new TlaModule(module.name, module.declarations ++ introConditions(inv.body))

      case Some(decl: TlaOperDecl) =>
        val message = s"Expected a nullary operator $invName, found ${decl.formalParams.length} arguments"
        throw new MalformedTlaError(message, decl.body)

      case Some(decl) =>
        val message = s"Expected a nullary operator $invName, found ${decl.getClass.getSimpleName}"
        throw new MalformedTlaError(message, NullEx)

      case None =>
        throw new MalformedTlaError(s"Invariant candidate $invName not found", NullEx)
    }
  }

  private def introConditions(inputInv: TlaEx): Seq[TlaOperDecl] = {
    def mapToDecls(smallInv: TlaEx, index: Int): Seq[TlaOperDecl] = {
      val deepCopy = DeepCopy(tracker)
      val positive = TlaOperDecl(NormalizedNames.VC_INV_PREFIX + index, List(), deepCopy.deepCopyEx(smallInv))
      val negative = TlaOperDecl(NormalizedNames.VC_NOT_INV_PREFIX + index, List(), tla.not(deepCopy.deepCopyEx(smallInv)))
      Seq(positive, negative)
    }

    val fragments = splitInv(Seq(), inputInv)
    logger.info(s"  > VCGen produced ${fragments.length} verification condition(s)")
    fragments.zipWithIndex.flatMap { case (e, i) => mapToDecls(e, i) }
  }

  private def splitInv(universalsRev: Seq[(String, TlaEx)], inv: TlaEx): Seq[TlaEx] = {
    inv match {
      case OperEx(TlaBoolOper.forall, NameEx(varName), set, pred) =>
        // \A x \in S: B /\ C is equivalent to (\A x \in S: B) /\ (\A x \in S: C)
        splitInv((varName, set) +: universalsRev, pred)

      case OperEx(TlaBoolOper.and, args @ _*) =>
        // we split A /\ B into the set {A, B}
        args.flatMap(splitInv(universalsRev, _))

      case _ =>
        // nothing to split, just add quantifiers that were collected on the way
        Seq(decorateWithUniversals(universalsRev, inv))
    }
  }

  private def decorateWithUniversals(universalsRev: Seq[(String, TlaEx)], expr: TlaEx): TlaEx = {
    universalsRev match {
      case Nil =>
        expr

      case (name, set) :: tail =>
        decorateWithUniversals(tail, tla.forall(NameEx(name), set, expr))
    }
  }
}
