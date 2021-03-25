package at.forsyte.apalache.tla.typedbuilder

import at.forsyte.apalache.tla.lir.{TlaEx, _}
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.values._

class TypeTag1Synthesizer extends TagSynthesizer {
  override def validateTagDomain(tag: TypeTag): Unit = tag match {
    case Typed(_: TlaType1) => // all good
    case other =>
      throw new TypingException(
          s"Expecting a TlaType1 tag, found $other."
      )
  }

  override def validateParameterTags(taggedParams: Traversable[TaggedParameter]): Unit =
    taggedParams foreach TaggedParameter.assertValidType1Tag

  override def synthesizeOperatorTag(oper: TlaOper, args: TlaEx*): TypeTag =
    TT1OperatorSignatureMatcher.matchSignature(oper, args) match {
      case Some(tt1) => Typed(tt1)
      case None =>
        throw new TypingException(
            s"Arguments $args to operator ${oper.name} do not match that operator's signature."
        )
    }

  override def synthesizeValueTag(v: TlaValue): TypeTag = {
    val tagType: TlaType1 = v match {
      case TlaInt(_)     => IntT1()
      case TlaDecimal(_) => RealT1()
      case TlaReal()     => RealT1()
      case TlaBool(_)    => BoolT1()
      case TlaStr(_)     => StrT1()

      case TlaBoolSet => SetT1(BoolT1())
      case TlaStrSet  => SetT1(StrT1())
      case TlaIntSet  => SetT1(IntT1())
      case TlaNatSet  => SetT1(IntT1())
      case TlaRealSet => SetT1(RealT1())
    }
    Typed(tagType)
  }

  override def synthesizeDeclarationTag(paramTags: Traversable[TypeTag], bodyTag: TypeTag): TypeTag = {
    // assume validation
    val paramTypes = paramTags.toSeq.map { asTlaType1 }
    val bodyType = asTlaType1(bodyTag)

    Typed(OperT1(paramTypes, bodyType))
  }
}
