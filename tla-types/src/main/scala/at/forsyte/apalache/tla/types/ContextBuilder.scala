package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.UID

/**
  * ContextBuilder keeps track of which SmtDatatype (mostly SmtTypeVar) gets assigned
  * to which UID, within a given operator application stack.
  *
  * Because the same operator may be invoked in multiple places, we cannot statically assign
  * SmtDatatypes to UIDs of subexpressions of operator bodies,
  * but must perform a per-call-site (or, more generally, per-stack-of-call-sites) analysis
  */
class ContextBuilder {
  private var context : OperatorContext = Map.empty

  def record(
              operStack : OperatorApplicationStack,
              id : UID,
              x : SmtDatatype
            ) : Unit = {
    val newMap = context.getOrElse( operStack, Map.empty ) + ( id -> x )
    context = context.updated( operStack, newMap )
  }

  def get : OperatorContext = context
}
