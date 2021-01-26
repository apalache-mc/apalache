package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.standard.KeraLanguagePred
import at.forsyte.apalache.tla.lir.transformations.{
  LanguageWatchdog,
  TlaExTransformation,
  TransformationTracker
}
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
  *    Can we integrate this class into the type system?</p>
  *
  * @author Igor Konnov
  */
class ExpansionMarker @Inject()(tracker: TransformationTracker)
    extends TlaExTransformation
    with LazyLogging {

  override def apply(e: TlaEx): TlaEx = {
    LanguageWatchdog(KeraLanguagePred()).check(e)
    transform(shallExpand = false)(e)
  }

  // By default, the expressions are not wrapped with 'Expand'. Once the function crosses the border of an expression
  // that requires an expanded set, e.g., S \\union (SUBSET T), the parameter shallExpand changes to true.
  def transform(shallExpand: Boolean): TlaExTransformation = tracker.trackEx {
    case ex @ OperEx(op @ TlaSetOper.powerset, underlyingSet) =>
      if (shallExpand) {
        // Expand the set as well as the underlying set!
        logger.warn(
          s"The set $ex will be expanded. This will blow up the solver."
        )
        OperEx(BmcOper.expand, OperEx(op, transform(true)(underlyingSet)))
      } else {
        // Do not expand the set itself, but expand the underlying set!
        OperEx(op, transform(true)(underlyingSet))
      }

    case ex @ OperEx(op @ TlaSetOper.funSet, dom, cdm) =>
      if (shallExpand) {
        // Expand everything, including the function set.
        logger.warn(
          s"The set $ex will be expanded. This will blow up the solver."
        )
        OperEx(
          BmcOper.expand,
          OperEx(op, transform(true)(dom), transform(true)(cdm))
        )
      } else {
        // Only expand the domain, but keep the co-domain unexpanded,
        // e.g., in [SUBSET S -> SUBSET T], while SUBSET S is expanded, the co-domain SUBSET T can be left as is
        OperEx(op, transform(true)(dom), transform(false)(cdm))
      }

    // simple propagation analysis that tells us what to expand
    case OperEx(
        op @ BmcOper.`skolem`,
        OperEx(TlaBoolOper.exists, name, set, pred)
        ) =>
      // a skolemizable existential is allowed to keep its set unexpanded
      OperEx(
        op,
        OperEx(
          TlaBoolOper.exists,
          name,
          transform(false)(set),
          transform(false)(pred)
        )
      )

    case OperEx(op @ TlaOper.chooseBounded, name, set, pred) =>
      // CHOOSE is essentially a skolemizable existential with the constraint of uniqueness
      OperEx(op, name, transform(false)(set), transform(false)(pred))

    case OperEx(op, name, set, pred)
        if op == TlaBoolOper.exists || op == TlaBoolOper.forall =>
      // non-skolemizable quantifiers require their sets to be expanded
      OperEx(op, name, transform(true)(set), transform(false)(pred))

    case OperEx(op @ TlaSetOper.in, elem, set) =>
      // when checking e \in S, we can keep S unexpanded, but e should be expanded
      OperEx(op, transform(true)(elem), transform(false)(set))

    case OperEx(op, args @ _*)
        if op == TlaSetOper.cup || op == TlaSetOper.union =>
      // binary union and UNION require arena cells, hence, expand
      OperEx(op, args map transform(true): _*)

    case OperEx(op @ TlaSetOper.filter, name, set, pred) =>
      // For the moment, we require the set to be expanded. However, we could think of collecting constraints on the way.
      OperEx(op, name, transform(true)(set), transform(false)(pred))

    case OperEx(op, body, args @ _*)
        if op == TlaSetOper.map || op == TlaFunOper.funDef || op == TlaFunOper.recFunDef =>
      val tbody: TlaEx = transform(false)(body)
      val targs = args map transform(true)
      OperEx(op, tbody +: targs: _*)

    case LetInEx(body, defs @ _*) =>
      // at this point, we only have nullary let-in definitions
      def mapDef(df: TlaOperDecl) = {
        TlaOperDecl(df.name, df.formalParams, transform(shallExpand)(df.body))
      }

      LetInEx(transform(shallExpand)(body), defs map mapDef: _*)

    case OperEx(BmcOper.withType, expr, annot) =>
      // transform the expression, but not the annotation! See https://github.com/informalsystems/apalache/issues/292
      OperEx(BmcOper.withType, transform(shallExpand)(expr), annot)

    case OperEx(oper, args @ _*) =>
      // try to descend in the children, which may contain Boolean operations, e.g., { \E x \in S: P }
      OperEx(oper, args map transform(shallExpand): _*)

    case terminal =>
      terminal // terminal expression, stop here
  }

}
