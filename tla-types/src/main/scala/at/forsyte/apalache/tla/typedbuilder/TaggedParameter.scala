package at.forsyte.apalache.tla.typedbuilder

import at.forsyte.apalache.tla.lir.{
  BuilderError, FormalParam, LirError, OperFormalParam, OperT1, SimpleFormalParam, TlaType1, TypeTag, Typed,
  TypingException
}

sealed case class TaggedParameter(param: FormalParam, paramTag: TypeTag)

object TaggedParameter {
  def assertValidType1Tag(taggedParam: TaggedParameter): Unit = {
    // Note: we don't perform more sophisticated checks, e.g. making sure
    // simple paramters aren't actually higher-order, we just make sure OFP are
    // at least operator-typed, for now

    val pName = taggedParam.param.name

    taggedParam.paramTag match {
      case Typed(paramType: TlaType1) =>
        taggedParam.param match {
          case OperFormalParam(_, arity) =>
            paramType match {
              case OperT1(operArgTypes, _) =>
                val nArgsInType = operArgTypes.size
                if (nArgsInType != arity)
                  throw new TypingException(
                      s"Operator parameter $pName of arity $arity annotated with operator type of arity $nArgsInType."
                  )
              case _ =>
                throw new TypingException(
                    s"Operator parameter $pName not annotated with operator type."
                )
            }
          case _: SimpleFormalParam => ()
        }
      case x =>
        throw new TypingException(
            s"Expected a TlaType1 tag for $pName, found $x."
        )
    }
  }

}
