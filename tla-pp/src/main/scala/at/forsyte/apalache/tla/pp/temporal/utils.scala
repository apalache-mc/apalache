package at.forsyte.apalache.tla.pp.temporal

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.Flatten

/**
 * A convenience class storing a module, together with the init, next and loopOK predicates of that module. Useful to
 * avoid re-finding these predicates.
 */
case class ModWithPreds(
    val module: TlaModule,
    val init: TlaOperDecl,
    val next: TlaOperDecl,
    val loopOK: TlaOperDecl) {}

/**
 * A convenience class for packing conjuncts that make up the init, next and loopOK predicates. Useful for collecting
 * these expressions without adding them to the predicates one by one, to later add them all at once.
 */
case class PredExs(
    val initExs: Seq[TBuilderInstruction] = Seq.empty,
    val nextExs: Seq[TBuilderInstruction] = Seq.empty,
    val loopOKExs: Seq[TBuilderInstruction] = Seq.empty) {

  def ++(that: PredExs): PredExs = {
    PredExs(
        this.initExs ++ that.initExs,
        this.nextExs ++ that.nextExs,
        this.loopOKExs ++ that.loopOKExs,
    )
  }
}

package object utils {
  val builder: ScopedBuilder = new ScopedBuilder()
}

object DeclUtils {
  import at.forsyte.apalache.tla.pp.temporal.utils.builder

  /**
   * Takes decl, ex and returns newDecl with the same name as decl, with its body extended like this: newDecl == decl /\
   * ex
   */
  def andInDecl(ex: TBuilderInstruction, decl: TlaOperDecl, tracker: TransformationTracker): TlaOperDecl = {
    val newBody =
      Flatten(tracker)(Typed(BoolT1))(
          builder.and(
              builder.unchecked(decl.body),
              ex,
          )
      )
    decl.copy(body = newBody)
  }
}
