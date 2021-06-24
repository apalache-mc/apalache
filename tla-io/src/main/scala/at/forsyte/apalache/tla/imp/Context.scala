package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.io.UTFPrinter

import scala.annotation.tailrec

/**
 * A unit that a context can hold, e.g., a TLA+ declaration.
 */
abstract class ContextUnit {
  def name: String
}

/**
 * The most common case of a context unit is a TLA+ declaration.
 *
 * @param decl the attached declaration
 */
case class DeclUnit(decl: TlaDecl) extends ContextUnit {
  override def name: String = decl.name
}

/**
 * This is a declaration that serves as an alias for an operator in the standard library,
 * e.g., if the user writes I = INSTANCE Integers and then I!+(a, b), then I!+ is an alias for TlaArithOper.plus.
 *
 * @param alias the alias
 * @param oper a built-in operator that is bound to the alias.
 */
case class OperAliasUnit(alias: String, oper: TlaOper) extends ContextUnit {
  override def name: String = alias
}

/**
 * This is a declaration that serves as an alias for a value in the standard library.
 * Although TLA+ does not distinguish between values and operators, we do.
 *
 * @param alias the alias
 * @param tlaValue a TLA+ value to associate with the alias
 */
case class ValueAliasUnit(alias: String, tlaValue: TlaValue) extends ContextUnit {
  override def name: String = alias
}

/**
 * An empty declaration. We use NoneUnit to avoid redundancy when need Option[ContextUnit].
 */
case class NoneUnit() extends ContextUnit {
  override val name: String = ""
}

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

  /**
   * Append a declaration unit in the context.
   *
   * @param unit a declaration unit
   * @return a new context that contains the declarations of this context and the new unit
   */
  def push(unit: ContextUnit): Context

  /**
   * Get all declarations in the context, in the same order as they were added to the context.
   *
   * @return a list of declaration units
   */
  def declarations: List[ContextUnit]

  /**
   * Find a declaration that is associated with the name. If the context is given a lookup prefix "A!B!C", then
   * lookup("x") will try "A!B!C!x", "B!C!x", "C!x", "x", in that order.
   *
   * @param name a name that may be prefixed with instance names, e.g., A!B!x
   * @return the declaration, if found
   */
  def lookup(name: String): ContextUnit

  /**
   * Return a copy of the context that is tuned to the lookup prefix, e.g., ["A", "B", "C"]. This lookup prefix is
   * used for resolving declaration names, see lookup.
   * @param prefix a sequence of instance names.
   * @return a copy of the context
   */
  def setLookupPrefix(prefix: List[String]): Context

  /**
   * Get the lookup prefix that represents the instantiation path from the root module down to the instances
   *
   * @return the sequence of instance names
   */
  val lookupPrefix: List[String]

  /**
   * Add all definitions from the other context. We assume that the keys in the both contexts do not intersect.
   * If the keys intersect, an implementation is free to throw an IllegalStateException at some point...
   *
   * @param other the other context
   */
  def disjointUnion(other: Context): Context

  /**
   * Sometimes, the importer has to add a prefix to a declaration name, to guarantee the name uniqueness.
   * For instance, when we translate a LOCAL operator as a LET-IN expression, we may introduce a name collision.
   * Node translators may add the lookup prefix, when this flag is set to true.
   *
   * @param flag whether to add the lookup prefix to names.
   * @return a new context that has the flag set to the value.
   */
  def setUseQualifiedNames(flag: Boolean): Context

  /**
   * Depending on the value of `useQualifiedNames`, produce either a fully qualified name, or keep the short name.
   *
   * @param name a non-qualified name
   * @return either a qualified name or the passed name, depending on the value of `useQualifiedNames`
   */
  def mkQualifiedNameIfAsked(name: String): String
}

object Context {

  /**
   * Create a new context, i.e., use Context().
   */
  def apply(): Context = {
    new ContextImpl(List(), false, List(), Map())
  }

  def apply(mod: TlaModule): Context = {
    var context = mod.constDeclarations.foldLeft(Context()) { (c, d) =>
      c.push(DeclUnit(d))
    }
    context = mod.varDeclarations.foldLeft(context) { (c, d) =>
      c.push(DeclUnit(d))
    }
    context = mod.operDeclarations.foldLeft(context) { (c, d) =>
      c.push(DeclUnit(d))
    }
    context = mod.assumeDeclarations.foldLeft(context) { (c, d) =>
      c.push(DeclUnit(d))
    }
    context
  }

  // the actual implementation that otherwise would have disclosed the implementation details via its constructor.
  private class ContextImpl(val lookupPrefix: List[String], val useQualifiedNames: Boolean,
      val revList: List[ContextUnit], val unitMap: Map[String, ContextUnit])
      extends Context {
    // fwdList lazily stores values in the (expected) forward order, whereas revList stores the values
    // in the reverse order, which is optimized for push.
    private var fwdList: Option[List[ContextUnit]] = None

    def push(decl: ContextUnit): Context = {
      unitMap.get(decl.name).collect {
        case dup if dup != decl =>
          val printer = UTFPrinter
          val dupS = printer(dup.asInstanceOf[DeclUnit].decl)
          val declS = printer(decl.asInstanceOf[DeclUnit].decl)
          throw new MalformedSepecificationError(
              s"Found two different declarations with the same name [${decl.name}]: [$dupS] and [$declS].")
      }

      val newList = decl :: revList
      new ContextImpl(lookupPrefix, useQualifiedNames, newList, unitMap + (decl.name -> decl))
    }

    override def lookup(name: String): ContextUnit = {
      @tailrec
      def findRec(qname: String): ContextUnit = {
        unitMap.get(qname) match {
          case Some(u) => u

          case None =>
            val index = qname.indexOf("!")
            if (index < 0) {
              NoneUnit()
            } else {
              findRec(qname.substring(index + 1))
            }
        }
      }

      val fullname = (lookupPrefix :+ name).mkString("!")
      findRec(fullname)
    }

    override def setLookupPrefix(prefix: List[String]): Context = {
      val copy = new ContextImpl(prefix, useQualifiedNames, revList, unitMap)
      copy
    }

    def declarations: List[ContextUnit] = {
      fwdList match {
        case Some(list) =>
          list

        case None =>
          val list = revList.reverse
          fwdList = Some(list)
          list
      }
    }

    override def disjointUnion(other: Context): Context = {
      other match {
        case that: ContextImpl =>
          new ContextImpl(lookupPrefix, useQualifiedNames, revList ++ that.revList, unitMap ++ that.unitMap)

        case _ =>
          // we could have implemented it, but there is only one implementation of Context.
          throw new RuntimeException("Merging two different implementations of Context...")
      }
    }

    override def setUseQualifiedNames(flag: Boolean): Context = {
      new ContextImpl(lookupPrefix, flag, revList, unitMap)
    }

    override def mkQualifiedNameIfAsked(name: String): String = {
      if (useQualifiedNames) {
        (lookupPrefix :+ name).mkString("!")
      } else {
        name
      }
    }
  }
}
