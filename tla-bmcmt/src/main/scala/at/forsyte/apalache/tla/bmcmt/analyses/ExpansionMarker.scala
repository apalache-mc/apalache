package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.standard.KeraLanguagePred
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TlaExTransformation, TransformationTracker}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * <p>This analysis tracks down the exponentially expensive expressions such as SUBSET S and [S -> T].
 * When such an expression has to be expanded in the arena, the expression is wrapped with BmcOper!Expand.
 * The user also receives a warning that this operation is going to be expensive.</p>
 *
 * <p>TODO: This is a simple form of constraint generation. Perhaps, we should lift the rewriting framework
 * to collecting constraints, rather than eagerly and lazily expanding the sets.</p>
 *
 * <p>It is a simple form of type inference on top of our type system.
 * Can we integrate this class into the type system?</p>
 *
 * @author Igor Konnov
 */
class ExpansionMarker @Inject() (tracker: TransformationTracker) extends TlaExTransformation with LazyLogging {

  override def apply(e: TlaEx): TlaEx = {
    LanguageWatchdog(KeraLanguagePred()).check(e)
    transform(shallExpand = false)(e)
  }

  // By default, the expressions are not wrapped with 'Expand'. Once the function crosses the border of an expression
  // that requires an expanded set, e.g., S \\union (SUBSET T), the parameter shallExpand changes to true.
  def transform(shallExpand: Boolean): TlaExTransformation = tracker.trackEx {
    case ex @ OperEx(op @ TlaSetOper.powerset, underlyingSet) =>
      val tag = ex.typeTag
      if (shallExpand) {
        // Expand the set as well as the underlying set!
        logger.warn(s"The set $ex will be expanded. This will blow up the solver.")
        OperEx(ApalacheOper.expand, OperEx(op, transform(true)(underlyingSet))(tag))(tag)
      } else {
        // Do not expand the set itself, but expand the underlying set!
        OperEx(op, transform(true)(underlyingSet))(tag)
      }

    case ex @ OperEx(op @ TlaSetOper.funSet, dom, cdm) =>
      val tag = ex.typeTag
      if (shallExpand) {
        // Expand everything, including the function set.
        logger.warn(s"The set $ex will be expanded. This will blow up the solver.")
        OperEx(ApalacheOper.expand, OperEx(op, transform(true)(dom), transform(true)(cdm))(tag))(tag)
      } else {
        // Only expand the domain, but keep the co-domain unexpanded,
        // e.g., in [SUBSET S -> SUBSET T], while SUBSET S is expanded, the co-domain SUBSET T can be left as is
        OperEx(op, transform(true)(dom), transform(false)(cdm))(tag)
      }

    // simple propagation analysis that tells us what to expand
    case ex @ OperEx(op @ ApalacheOper.`skolem`, OperEx(TlaBoolOper.exists, name, set, pred)) =>
      // a skolemizable existential is allowed to keep its set unexpanded
      val tag = ex.typeTag
      OperEx(op, OperEx(TlaBoolOper.exists, name, transform(false)(set), transform(false)(pred))(tag))(tag)

    case ex @ OperEx(op @ TlaOper.chooseBounded, name, set, pred) =>
      // CHOOSE is essentially a skolemizable existential with the constraint of uniqueness
      val tag = ex.typeTag
      OperEx(op, name, transform(false)(set), transform(false)(pred))(tag)

    case ex @ OperEx(op, name, set, pred) if op == TlaBoolOper.exists || op == TlaBoolOper.forall =>
      // non-skolemizable quantifiers require their sets to be expanded
      val tag = ex.typeTag
      OperEx(op, name, transform(true)(set), transform(false)(pred))(tag)

    case ex @ OperEx(op, elem, set)
        if op == TlaSetOper.in || op == ApalacheOper.selectInSet || op == ApalacheOper.storeInSet || op == TlaSetOper.notin || op == ApalacheOper.unchangedSet =>
      // when checking e \in S or e \notin S, we can keep S unexpanded, but e should be expanded
      val tag = ex.typeTag
      OperEx(op, transform(true)(elem), transform(false)(set))(tag)

    case ex @ OperEx(op, args @ _*) if op == TlaSetOper.cup || op == TlaSetOper.union =>
      // binary union and UNION require arena cells, hence, expand
      val tag = ex.typeTag
      OperEx(op, args map transform(true): _*)(tag)

    case ex @ OperEx(op @ TlaSetOper.filter, name, set, pred) =>
      // For the moment, we require the set to be expanded. However, we could think of collecting constraints on the way.
      val tag = ex.typeTag
      OperEx(op, name, transform(true)(set), transform(false)(pred))(tag)

    case ex @ OperEx(op, body, args @ _*)
        if op == TlaSetOper.map || op == TlaFunOper.funDef || op == TlaFunOper.recFunDef =>
      val tbody: TlaEx = transform(false)(body)
      val targs = args map transform(true)
      val tag = ex.typeTag
      OperEx(op, tbody +: targs: _*)(tag)

    case ex @ LetInEx(body, defs @ _*) =>
      // at this point, we only have nullary let-in definitions
      def mapDef(df: TlaOperDecl) = df.copy(body = transform(shallExpand)(df.body))

      val tag = ex.typeTag
      LetInEx(transform(shallExpand)(body), defs map mapDef: _*)(tag)

    case ex @ OperEx(oper, args @ _*) =>
      // try to descend in the children, which may contain Boolean operations, e.g., { \E x \in S: P }
      val tag = ex.typeTag
      OperEx(oper, args map transform(shallExpand): _*)(tag)

    case terminal =>
      terminal // terminal expression, stop here
  }

}
