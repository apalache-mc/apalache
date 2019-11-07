package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaControlOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations.standard.{IncrementalRenaming, ReplaceFixed}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.TlaBool
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
  * A simple skolemization analysis that finds the existential quantifiers that stand freely in a formula, that is,
  * not located under any universal quantifier.
  *
  * @author Igor Konnov
  */
class SimpleSkolemization @Inject()
        (val frexStore: FreeExistentialsStoreImpl, tracker: TransformationTracker) extends LazyLogging {

  def label( decls : Traversable[TlaDecl] ) : Unit = decls foreach {
    case d : TlaOperDecl => markFreeExistentials( d.body )
    case _ => ()
  }

  private def markFreeExistentials(ex: TlaEx): Unit = ex match {
    case OperEx(TlaBoolOper.exists, name, _, pred) =>
      logger.debug(s"added free existential $name (id=${ex.ID})")
      frexStore.store += ex.ID
      markFreeExistentials(pred)

    case OperEx(TlaBoolOper.and, args@_*) =>
      args foreach markFreeExistentials

    case OperEx(TlaBoolOper.or, args@_*) =>
      args foreach markFreeExistentials

    case OperEx(TlaControlOper.ifThenElse, args@_*) =>
      // we do not have to check that the predicate does not have \forall,
      // as we are only concerned with \exists in the scope of \forall
      args foreach markFreeExistentials

    case _ =>
      () // stop here
  }

}
