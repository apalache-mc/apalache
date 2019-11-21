package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
  * <p>An abstract transformer that calls partial functions.<p>
  *
  * @author Igor Konnov
  */
abstract class AbstractTransformer(tracker: TransformationTracker) {
  /**
    * The sequence of partial transformers
    */
  protected val partialTransformers: Seq[PartialFunction[TlaEx, TlaEx]]

  /**
    * Transform an expression recursively by calling transformers that are implemented as partial functions.
    *
    * @return a new expression
    */
  def transform: TlaExTransformation = tracker.track {
    case OperEx(op, args @ _*) =>
      transformOneLevel(OperEx(op, args map transform :_*))

    case LetInEx(body, defs @ _*) =>
      def mapDecl(d: TlaOperDecl): TlaOperDecl = {
        TlaOperDecl(d.name, d.formalParams, transform(d.body))
      }

      LetInEx(transform(body), defs.map(mapDecl) :_*)

    case ex =>
      transformOneLevel(ex)
  }

  /**
    * Transform an expression without looking into the arguments.
    * @return a new expression
    */
  private def transformOneLevel: TlaExTransformation = {
    // chain partial functions to handle different types of operators with different functions
    tracker.track(allTransformers reduceLeft (_ orElse _))
  }

  private val identity: PartialFunction[TlaEx, TlaEx] = { case e => e }
  private lazy val allTransformers = partialTransformers :+ identity
}


