package at.forsyte.apalache.tla.typedbuilder

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper

trait TagSynthesizer {
  def validateTagDomain(tag: TypeTag): Unit
  def validateParameterTags(taggedParams: Traversable[TaggedParameter]): Unit

  def synthesizeOperatorTag(oper: TlaOper, args: TlaEx*): TypeTag
  def synthesizeValueTag(v: TlaValue): TypeTag
  def synthesizeDeclarationTag(
      paramTags: Traversable[TypeTag], bodyTag: TypeTag
  ): TypeTag
}

class UntypedSynthesizer extends TagSynthesizer {
  // Untyped doesn't care about types, so it doesn't complain on Typed(_) tags
  override def validateTagDomain(tag: TypeTag): Unit = ()
  // Untyped doesn't care about types, so it doesn't complain on Typed(_) tags
  override def validateParameterTags(taggedParams: Traversable[TaggedParameter]): Unit = ()

  override def synthesizeOperatorTag(oper: TlaOper, args: TlaEx*): TypeTag = Untyped()

  override def synthesizeValueTag(v: TlaValue): TypeTag = Untyped()

  override def synthesizeDeclarationTag(paramTags: Traversable[TypeTag], bodyTag: TypeTag): TypeTag = Untyped()
}
