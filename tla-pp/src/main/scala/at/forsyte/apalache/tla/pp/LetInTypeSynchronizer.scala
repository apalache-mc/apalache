package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaEx, Typed, TypingException}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.typecheck.etc.{Substitution, TypeUnifier}

/**
 * LetInTypeSynchronizer re-computes the types of any residual LET-IN defined operators, that were defined
 * in the scope of a polymorphic operator (e.g. in FoldX). After inlining, any leftover LET-IN operators should have monotypes
 */
class LetInTypeSynchronizer(tracker: TransformationTracker) extends TlaExTransformation {
  override def apply(ex: TlaEx): TlaEx = transform(ex)

  def transform: TlaExTransformation = tracker.trackEx {
    // interesting case
    case letInEx @ LetInEx(letInBody, defs @ _*) if defs.length == 1 =>
      // The problem with let-ins is that, while the body will have the correct monotype, the
      // type checking algorithm does not update the declaration and body tags.

      // The solution: Unify the body type and the declaration type, then apply the resulting substitution over the
      // declaration body
      val Seq(letInDecl) = defs
      val bodyType = letInBody.typeTag.asTlaType1()
      val declType = letInDecl.typeTag.asTlaType1()
      val unifiedOpt = (new TypeUnifier).unify(Substitution.empty, bodyType, declType)

      unifiedOpt match {
        case None => throw new TypingException("Could not synchronize type of fold operator.")
        case Some((subst, unifiedType)) =>
          val substitutor = new TypeSubstitutor(tracker, subst)
          val newDecl = letInDecl.copy(body = substitutor(letInDecl.body))(Typed(unifiedType))
          LetInEx(letInBody, newDecl)(Typed(unifiedType))
      }

    // recursive processing of composite operators
    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map transform
      if (isNoOp(args, newArgs)) ex else OperEx(op, newArgs: _*)(ex.typeTag)

    case ex => ex
  }

  private def isNoOp(args1: Seq[TlaEx], args2: Seq[TlaEx]): Boolean = {
    if (args1.length != args2.length)
      false
    else
      args1.map(_.ID).zip(args2.map(_.ID)).forall(pa => pa._1 == pa._2)
  }
}

object LetInTypeSynchronizer {
  def apply(tracker: TransformationTracker): LetInTypeSynchronizer = {
    new LetInTypeSynchronizer(tracker)
  }
}
