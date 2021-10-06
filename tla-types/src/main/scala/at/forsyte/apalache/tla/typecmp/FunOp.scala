package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir.{OperEx, SeqT1, TlaEx, TlaType1, TupT1}
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.typecheck.etc.Substitution

object FunOp {
  def tupCmp: pureTypeComputation = {
    TupT1(_: _*)
  }

  // Assume nonempty
  def seqCmp: pureTypeComputation = {
    case Nil =>
      throwMsg("Unable to determine sequence element type for empty sequence.")
    case h +: t if t.forall(_ == h) => SeqT1(h)
    case args =>
      throwMsg(s"Sequence expects arguments of type (T*), found: (${args.mkString(",")})")

  }

  def exceptCmp: typeComputation = { args =>
    val nArgs = args.length
    assert(nArgs >= 3 && nArgs % 2 == 1)
    // Each row lists all of the arguments that define one update,
    val argumentRows = args.zipWithIndex collect {
      case (OperEx(TlaFunOper.tuple, tupArgs @ _*), i) if i % 2 == 1 =>
        tupArgs
    }

    // Ensure that all of the arguments are uniformly sized
    val rowSizes = (argumentRows map {
      _.length
    }).toSet
    assert(rowSizes.size == 1)

    // The first argument is the applicative (fn/rec/seq/tup), the other even positions hold
    // the updates in the final codomain
    val applicativeCand +: codomainArgs = args.zipWithIndex collect {
      case (ex, i) if i % 2 == 0 =>
        ex
    }

    // The arguments match the signature of (multi-level) except, if the argument types consecutively unify
    // with the appropriate layer of applicativeCand.type
    def matchUpdateWithArgChain(guidingType: TlaType1, rowArgTypes: Seq[TlaEx], updateType: TlaType1,
        subst: Substitution = Substitution.empty): Option[(Substitution, TlaType1)] =
      rowArgTypes match {
        case Nil =>
          // If we've run out of arguments, guidingType has been peeled until the update layer
          // It must unify with the updateType
          singleUnification(guidingType, updateType)
        case headEx +: tailExs =>
          for {
            // Otherwise, `guidingType` must be some form of Applicative(fromT, toT).
            // As headEx is the argument at the current depth, its value gives us a hint for tuples/records.
            Applicative(fromT, toT) <- Applicative.asInstanceOfApplicative(guidingType, argHint = headEx)
            // The toT type, in the case of multi-level EXCEPT may be another applicative, so
            // we recurse with it over the other arguments given by tailExs.
            (subst1, _) <- matchUpdateWithArgChain(toT, tailExs, updateType, subst)
            // Lastly, the type of headEx must unify with the domain type at the current layer, fromT
            (subst2, _) <- singleUnification(TlaType1.fromTypeTag(headEx.typeTag), fromT, subst1)
            // If this process fails to unify at any step, we get None, otherwise we
            // have shown type compliance with guidingType at this layer (which may morph slightly under
            // the computed substitution)
          } yield (subst2, subst2.subRec(guidingType))
      }

    // We now analyze each update point in sequence.
    // A point is a pair (a,b), where a is a sequence of arguments to the Applicative of each layer
    // and b is the final codomain update.
    val finalMatch =
      argumentRows
        .zip(codomainArgs)
        .foldLeft(
            // the starting type for the result of except is the type of the 1st argument,
            // i.e. the object being updated
            Option((Substitution.empty, TlaType1.fromTypeTag(applicativeCand.typeTag)))
        ) {
          // For each point, we use matchUpdateWithArgChain to see if the given arguments/codomain value
          // unify with the type of the object being updated
          case (Some((subst, partialUnifApplicativeType)), (rowExs, codomainEx)) =>
            matchUpdateWithArgChain(
                partialUnifApplicativeType,
                rowExs,
                TlaType1.fromTypeTag(codomainEx.typeTag),
                subst
            )
          case _ => None
        }
    // Finally, we drop the substitution, as it is no longer needed
    finalMatch map { _._2 } match {
      case Some(tt) => tt
      case _        => throwMsg(s"Arguments passed to ${TlaFunOper.except.name} have incompatible types.")
    }

  }

}
