package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaModule}

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
  protected def declarationMap: Map[String, TlaDecl]

  /**
    * Find a declaration that is associated with the name. If the context is given a lookup prefix "A!B!C", then
    * lookup("x") will try "A!B!C!x", "B!C!x", "C!x", "x", in that order.
    *
    * @param name a name that may be prefixed with instance names, e.g., A!B!x
    * @return the declaration, if found
    */
  def lookup(name: String): Option[TlaDecl]

  /**
    * Return a copy of the context that is tuned to the lookup prefix, e.g., ["A", "B", "C"]. This lookup prefix is
    * used for resolving declaration names, see lookup.
    * @param prefix a sequence of instance names.
    * @return a copy of the context
    */
  def setLookupPrefix(prefix: List[String]): Context

  /**
    * Add all definitions from the other context. We assume that the keys in the both contexts do not intersect.
    * If the keys intersect, an implementation is free to throw an IllegalStateException at some point...
    *
    * @param other the other context
    */
  def disjointUnion(other: Context): Context
}

object Context {
  /**
    * Create a new context, i.e., use Context().
   */
  def apply(): Context = {
    new ContextImpl(List(), List())
  }

  def apply(mod: TlaModule): Context = {
    var context = mod.constDeclarations.foldLeft(Context()) { (c, d) => c.push(d) }
    context = mod.varDeclarations.foldLeft(context) { (c, d) => c.push(d) }
    context = mod.operDeclarations.foldLeft(context) { (c, d) => c.push(d) }
    context = mod.assumeDeclarations.foldLeft(context) { (c, d) => c.push(d) }
    context
  }

  // the actual implementation that otherwise would have disclosed the implementation details via its constructor.
  private class ContextImpl(val lookupPrefix: List[String], val revList: List[TlaDecl]) extends Context {
    // fwdList lazily stores values in the (expected) forward order, whereas revList stores the values
    // in the reverse order, which is optimized for push.
    private var fwdList: Option[List[TlaDecl]] = None
    // declarationsMap is also lazy
    private var lazyDeclarationMap: Option[Map[String, TlaDecl]] = None

    def push(decl: TlaDecl): Context = {
      val newList = decl :: revList
      new ContextImpl(lookupPrefix, newList)
    }


    /**
      * Find a declaration that is associated with the name. If the context is given a lookup prefix "A!B!C", then
      * lookup("x") will try "A!B!C!x", "B!C!x", "C!x", "x", in that order.
      *
      * @param name a name that may be prefixed with instance names, e.g., A!B!x
      * @return the declaration, if found
      */
    override def lookup(name: String): Option[TlaDecl] = {
      val map: Map[String, TlaDecl] = declarationMap
      def find(qname: String): Option[TlaDecl] = {
        if (map.contains(qname)) {
          Some(map(qname))
        } else {
          val index = qname.indexOf("!")
          if (index < 0 ) {
            None
          } else {
            find(qname.substring(index + 1))
          }
        }
      }

      val fullname = (lookupPrefix :+ name).mkString("!")
      find(fullname)
    }

    /**
      * Return a copy of the context that is tuned to the lookup prefix, e.g., ["A", "B", "C"]. This lookup prefix is
      * used for resolving declaration names, see lookup.
      *
      * @param prefix a sequence of instance names.
      * @return a copy of the context
      */
    override def setLookupPrefix(prefix: List[String]): Context = {
      val copy = new ContextImpl(prefix, revList)
      copy
    }


    override protected def declarationMap: Map[String, TlaDecl] = {
      lazyDeclarationMap match {
        case Some(map) =>
          map

        case None =>
          val map = revList.foldLeft(Map[String, TlaDecl]()) {
            (m, d) =>
              if (!m.contains(d.name))
                m + (d.name -> d)
              else
                throw new IllegalStateException(s"A duplicate key ${d.name} in the context!")
          }
          lazyDeclarationMap = Some(map)
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

    /**
      * Add all definitions from the other context. We assume that the keys in the both contexts do not intersect.
      * If the keys intersect, an implementation is free to throw an IllegalStateException any time later
      * (not necessarily in this method)...
      *
      * The lookup prefix is copied from the left-hand side.
      *
      * @param other the other context
      */
    override def disjointUnion(other: Context): Context = {
      other match {
        case that: ContextImpl =>
          new ContextImpl(lookupPrefix, revList ++ other.asInstanceOf[ContextImpl].revList)

        case _ =>
          // we could have implemented it, but there is the only implementation of Context.
          throw new RuntimeException("Merging two different implementations of Context...")
      }
    }
  }
}
