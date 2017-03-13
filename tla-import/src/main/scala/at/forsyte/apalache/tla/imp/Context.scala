package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.TlaDecl

/**
  * A translation context that contains the definitions of:
  * constants, variables, and operators. A context guarantees to store definitions in the order,
  * in which they have been added into the context.
  *
  * The contexts are immutable, that is, push creates a new context.
  *
  * @author konnov
  */
trait Context {
  def push(decl: TlaDecl): Context

  def declarations: List[TlaDecl]
  def declarationsMap: Map[String, TlaDecl]
}

object Context {
  /**
    * Create a new context, i.e., use Context().
   */
  def apply(): Context = {
    new ContextImpl(List())
  }

  // the actual implementation that otherwise would have disclosed the implementation details via its constructor.
  private class ContextImpl(revList: List[TlaDecl]) extends Context {
    // fwdList lazily stores values in the (expected) forward order, whereas revList stores the values
    // in the reverse order, which is optimized for push.
    private var fwdList: Option[List[TlaDecl]] = None
    // declarationsMap is also lazy
    private var declarationMap: Option[Map[String, TlaDecl]] = None

    def push(decl: TlaDecl): Context = {
      val newList = decl :: revList
      new ContextImpl(newList)
    }

    def declarationsMap: Map[String, TlaDecl] = {
      declarationMap match {
        case Some(map) =>
          map

        case None =>
          val map = revList.foldLeft(Map[String, TlaDecl]()) {
            (m, d) => m + (d.name -> d)
          }
          declarationMap = Some(map)
          map
      }
    }

    def declarations: List[TlaDecl] = {
      fwdList match {
        case Some(list) =>
          list

        case None =>
          val list = revList.reverse
          fwdList = Some(list)
          list
      }
    }
  }
}
