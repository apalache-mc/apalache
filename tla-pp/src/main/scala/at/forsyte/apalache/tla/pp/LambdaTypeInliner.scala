package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaDecl, TlaEx, TlaOperDecl, Typed, TypingException}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.typecheck.etc.{Substitution, TypeUnifier}

/**
 * LambdaTypeInliner re-computes the types of any residual LET-IN defined operators (i.e. lambdas),
 * that were defined in the scope of a polymorphic operator (e.g. in FoldX).
 * After inlining, any leftover LET-IN operators should have monotypes
 */
class LambdaTypeInliner(tracker: TransformationTracker) extends TlaExTransformation {
  override def apply(ex: TlaEx): TlaEx = transform(ex)

  /**
   * Selects the class of let-ins we wish to apply the transformation to.
   * At the moment, this includes lambdas, which have 1 declaration and are non-nullary
   */
  private def isRelevantLetInEx(letInEx: LetInEx): Boolean = {
    // currently, we only care about let-ins embedded in fold, which are nonnullary and single-def
    letInEx.decls.length == 1 && letInEx.decls.forall(_.formalParams.nonEmpty)
  }

  def transform: TlaExTransformation = tracker.trackEx {
    // interesting case
    case letInEx @ LetInEx(letInBody, defs @ _*) if isRelevantLetInEx(letInEx) =>
      // The problem with let-ins is that, while the body will have the correct monotype, the
      // type checking algorithm does not update the declaration and body tags.

      // The solution: Unify the body type and the declaration type, then apply the resulting substitution over the
      // declaration body
      val Seq(letInDecl) = defs
      val bodyType = letInBody.typeTag.asTlaType1()
      val declType = letInDecl.typeTag.asTlaType1()
      val unifiedOpt = (new TypeUnifier).unify(Substitution.empty, bodyType, declType)

      unifiedOpt match {
        case None =>
          // This should never happen, after #1088
          throw new TypingException("Could not synchronize type of fold operator.")
        case Some((subst, unifiedType)) =>
          val substitutor = new TypeSubstitutor(tracker, subst)
          val newDecl = letInDecl.copy(body = substitutor(letInDecl.body))(Typed(unifiedType))
          LetInEx(letInBody, newDecl)(Typed(unifiedType))
      }

    case letInEx @ LetInEx(letInBody, defs @ _*) =>
      // assume !isRelevant. This case covers nullary operators that were left after inlining
      // if keepNullary = true. These let-ins are treated the same way as the generic operator case,
      // however, we have to define noop scenarios in terms of types, not just IR equivalence
      val newBody = transform(letInBody)
      // Since this transformation can modify types only the scala == is insufficient.
      // Therefore, to check if the operation is a noop, we have to check ID equivalence everywhere
      val (newDefs, noop) = defs.foldLeft((Seq.empty[TlaOperDecl], true)) { case ((partialDefs, partialNoop), d) =>
        val newBody = transform(d.body)
        val withNew = partialDefs :+
          tracker
            .trackDecl { case decl: TlaOperDecl =>
              decl.copy(body = newBody)
            }(d)
            .asInstanceOf[TlaOperDecl]
        (withNew, partialNoop && newBody.ID == d.body.ID)
      }

      if (letInBody.eqTyped(newBody) && noop)
        letInEx
      else
        LetInEx(newBody, newDefs: _*)(newBody.typeTag)

    // recursive processing of composite operators
    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map transform
      if (isNoOp(args, newArgs)) ex else OperEx(op, newArgs: _*)(ex.typeTag)

    case ex => ex
  }

  /** A transformation which only modifies type tags is noop iff eqTyped holds for all pairs */
  private def isNoOp(args1: Seq[TlaEx], args2: Seq[TlaEx]): Boolean = {
    if (args1.length != args2.length)
      false
    else
      args1.zip(args2).forall(pa => pa._1.ID == pa._2.ID)
  }
}

object LambdaTypeInliner {
  def apply(tracker: TransformationTracker): LambdaTypeInliner = {
    new LambdaTypeInliner(tracker)
  }
}
