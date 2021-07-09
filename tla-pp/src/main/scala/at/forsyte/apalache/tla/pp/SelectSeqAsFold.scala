package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaActionOper, TlaControlOper, TlaFunOper, TlaOper, TlaSeqOper}
import at.forsyte.apalache.tla.lir.{
  BoolT1, LetInEx, NameEx, OperEx, OperParam, OperT1, SeqT1, TlaEx, TlaOperDecl, Typed, TypingException
}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
 * Replaces instances of SelectSeq, using the following definition:
 *
 * SelectSeq(seq, Test(_)) == LET CondAppend(s,e) == IF Test(e) THEN Append(s, e) ELSE s
 *                            IN FoldSeq( CondAppend, <<>>, seq )
 */
class SelectSeqAsFold(nameGenerator: UniqueNameGenerator, tracker: TransformationTracker) extends TlaExTransformation {

  override def apply(expr: TlaEx): TlaEx = {
    transform(expr)
  }

  def transform: TlaExTransformation = tracker.trackEx {
    case OperEx(TlaSeqOper.selectseq, seqEx, testNameEx @ NameEx(operName)) =>
      // Sanity check on types
      val seqElemType = seqEx.typeTag match {
        case Typed(SeqT1(a)) => a
        case badType         => throw new TypingException(s"Argument $seqEx expected to have type Seq(a), found $badType.")
      }

      testNameEx.typeTag match {
        case Typed(OperT1(Seq(`seqElemType`), BoolT1())) => () // all good
        case badType =>
          throw new TypingException(s"$operName expected to have type ($seqElemType) => Bool, found $badType.")
      }

      // Prep fresh names for the operator and its params
      val condAppOperName = nameGenerator.newName()
      val sParamName = nameGenerator.newName()
      val eParamName = nameGenerator.newName()

      def e(): NameEx = NameEx(eParamName)(Typed(seqElemType))
      def s(): NameEx = NameEx(sParamName)(seqEx.typeTag)

      // IF Test(e) THEN Append(s,e) ELSE s
      val condAppBody =
        OperEx(
            TlaControlOper.ifThenElse,
            OperEx(TlaOper.apply, testNameEx, e())(Typed(BoolT1())),
            OperEx(TlaSeqOper.append, s(), e())(seqEx.typeTag),
            s()
        )(seqEx.typeTag)

      val condAppDecl =
        TlaOperDecl(
            condAppOperName,
            List(sParamName, eParamName) map { s => OperParam(s) },
            condAppBody
        )(Typed(OperT1(Seq(SeqT1(seqElemType), seqElemType), SeqT1(seqElemType))))

      val foldEx =
        OperEx(
            ApalacheOper.foldSeq,
            NameEx(condAppOperName)(condAppDecl.typeTag),
            OperEx(TlaFunOper.tuple)(seqEx.typeTag),
            seqEx
        )(seqEx.typeTag)

      LetInEx(foldEx, condAppDecl)(foldEx.typeTag)

    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map transform
      if (args == newArgs) ex else OperEx(op, newArgs: _*)(ex.typeTag)

    case ex @ LetInEx(body, defs @ _*) =>
      // Transform bodies of all op.defs
      val newDefs = defs map tracker.trackOperDecl { d => d.copy(body = transform(d.body)) }
      val newBody = transform(body)
      if (defs == newDefs && body == newBody) ex else LetInEx(newBody, newDefs: _*)(ex.typeTag)
    case ex => ex
  }

}

object SelectSeqAsFold {
  def apply(gen: UniqueNameGenerator, tracker: TransformationTracker): SelectSeqAsFold = {
    new SelectSeqAsFold(gen, tracker)
  }
}
