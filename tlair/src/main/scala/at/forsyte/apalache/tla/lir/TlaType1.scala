package at.forsyte.apalache.tla.lir

import scala.collection.immutable.SortedMap

/**
 * Trait for a type in Type System 1 as specified in
 * <a href="https://github.com/informalsystems/apalache/blob/unstable/docs/adr/002adr-types.md">ADR-002</a>.
 */
sealed trait TlaType1 {

  /**
   * Compute the set of the names used in the type. These are names declared with VarT1.
   *
   * @return the set of variable names (actually, integers) that are used in the type.
   */
  def usedNames: Set[Int]
}

object TlaType1 {
  def fromTypeTag(typeTag: TypeTag): TlaType1 = {
    typeTag match {
      case Typed(tt: TlaType1) => tt
      case _                   => throw new TypingException("Expected Typed(_: TlaType1), found: " + typeTag)
    }
  }
}

/**
 * An integer type.
 */
case class IntT1() extends TlaType1 {
  override def toString: String = "Int"

  override def usedNames: Set[Int] = Set.empty

}

/**
 * An real type.
 */
case class RealT1() extends TlaType1 {
  override def toString: String = "Real"

  override def usedNames: Set[Int] = Set.empty

}

/**
 * A Boolean type.
 */
case class BoolT1() extends TlaType1 {
  override def toString: String = "Bool"

  override def usedNames: Set[Int] = Set.empty

}

/**
 * The type of an uninterpreted string literal.
 */
case class StrT1() extends TlaType1 {
  override def toString: String = "Str"

  override def usedNames: Set[Int] = Set.empty

}

/**
 * An uninterpreted type constant.
 *
 * @param name unique name of the constant type
 */
case class ConstT1(name: String) extends TlaType1 {
  require(name.forall(c => c.isUpper || c.isDigit || c == '_'),
      "ConstT1 accepts identifiers in upper case, found: " + name)

  override def toString: String = name

  override def usedNames: Set[Int] = Set.empty

}

/**
 * A type variable. Instead of using strings for names, we are just using integers, which makes it easier
 * to process them. To make vars user-friendly, we assign the names a..z to the numbers 0..25.
 * The rest are called a27, a28, etc.
 *
 * @param no the variable number
 */
case class VarT1(no: Int) extends TlaType1 {
  require(no >= 0, "Variable identifier must be non-negative, found: " + no)

  override def toString: String = {
    if (no >= 0 && no < VarT1.QNAMES.length) {
      VarT1.QNAMES(no)
    } else {
      "a" + no
    }
  }

  override def usedNames: Set[Int] = Set(no)

}

object VarT1 {
  // human-friendly names of the first 26 variables
  protected val QNAMES: Vector[String] = Vector("a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n",
      "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z")

  /**
   * Construct a variable from the human-readable form like 'b' or 'a100'.
   * We use this method to write human-readable variable names in tests.
   *
   * @param name a human-readable name
   * @return the variable that matches to that name
   */
  def parse(name: String): VarT1 = {
    val len = name.length
    if (len < 1) {
      throw new IllegalArgumentException("Expected either a lower-case letter or a[0-9]+, found: " + name)
    } else if (len == 1) {
      val index = QNAMES.indexOf(name)
      if (index >= 0) {
        VarT1(index)
      } else {
        throw new IllegalArgumentException("Expected a lower-case letter or a[0-9]+, found: " + name)
      }
    } else {
      if (name(0) != 'a') {
        throw new IllegalArgumentException("Expected either a lower-case letter or a[0-9]+, found: " + name)
      }
      try {
        val no = Integer.parseUnsignedInt(name.substring(1))
        VarT1(no)
      } catch {
        case _: NumberFormatException =>
          throw new IllegalArgumentException("Expected either a lower-case letter or a[0-9]+, found: " + name)
      }
    }
  }

  /**
   * Call parse(text).
   *
   * @param text a string representation of a variable
   * @return the variable, if text is in the right format. Otherwise, throw IllegalArgumentException.
   */
  def apply(text: String): VarT1 = {
    parse(text)
  }

  /**
   * Is the provided string a valid variable name
   *
   * @param text a string
   * @return true if `text` is a valid variable name
   */
  def isValidName(text: String): Boolean = {
    try {
      parse(text)
      true
    } catch {
      case _: IllegalArgumentException =>
        false
    }
  }
}

/**
 * A function type.
 *
 * @param arg the type of the argument; multiple arguments should be written as a tuple
 * @param res the type of the result
 */
case class FunT1(arg: TlaType1, res: TlaType1) extends TlaType1 {
  // always wrap a function with parenthesis, to make it non-ambiguous
  override def toString: String = s"($arg -> $res)"

  override def usedNames: Set[Int] = arg.usedNames ++ res.usedNames

}

/**
 * A set type.
 *
 * @param elem the type of the elements
 */
case class SetT1(elem: TlaType1) extends TlaType1 {
  override def toString: String = s"Set($elem)"

  override def usedNames: Set[Int] = elem.usedNames

}

/**
 * A sequence type.
 *
 * @param elem the type of the elements.
 */
case class SeqT1(elem: TlaType1) extends TlaType1 {
  override def toString: String = s"Seq($elem)"

  override def usedNames: Set[Int] = elem.usedNames

}

/**
 * A tuple type.
 *
 * @param elems a sequence of the element types
 */
case class TupT1(elems: TlaType1*) extends TlaType1 {
  override def toString: String = {
    val elemStrs = elems.map(_.toString)
    "<<%s>>".format(elemStrs.mkString(", "))
  }

  override def usedNames: Set[Int] = elems.foldLeft(Set[Int]()) { (s, t) =>
    s ++ t.usedNames
  }
}

/**
 * A sparse tuple type. The keys are sorted by their names.
 *
 * @param fieldTypes a sorted map from field names to their types
 */
case class SparseTupT1(fieldTypes: SortedMap[Int, TlaType1]) extends TlaType1 {
  override def toString: String = {
    val keyTypeStrs = fieldTypes.map(p => "%s: %s".format(p._1, p._2))
    "{%s}".format(keyTypeStrs.mkString(", "))
  }

  override def usedNames: Set[Int] = fieldTypes.values.foldLeft(Set[Int]()) { (s, t) =>
    s ++ t.usedNames
  }

}

object SparseTupT1 {
  def apply(keysAndTypes: (Int, TlaType1)*): SparseTupT1 = {
    SparseTupT1(SortedMap(keysAndTypes: _*))
  }
}

/**
 * A record type. The keys are sorted by their names.
 *
 * @param fieldTypes a sorted map from field names to their types
 */
case class RecT1(fieldTypes: SortedMap[String, TlaType1]) extends TlaType1 {
  override def toString: String = {
    val keyTypeStrs = fieldTypes.map(p => "%s: %s".format(p._1, p._2))
    "[%s]".format(keyTypeStrs.mkString(", "))
  }

  override def usedNames: Set[Int] = fieldTypes.values.foldLeft(Set[Int]()) { (s, t) =>
    s ++ t.usedNames
  }

}

object RecT1 {
  def apply(keysAndTypes: (String, TlaType1)*): RecT1 = {
    RecT1(SortedMap(keysAndTypes: _*))
  }
}

/**
 * An operator type.
 *
 * @param args the arguments' types
 * @param res  the result type
 */
case class OperT1(args: Seq[TlaType1], res: TlaType1) extends TlaType1 {
  override def toString: String = {
    val argStrs = args.map(_.toString)
    "((%s) => %s)".format(argStrs.mkString(", "), res.toString)
  }

  override def usedNames: Set[Int] = res.usedNames ++ args.foldLeft(Set[Int]()) { (s, t) =>
    s ++ t.usedNames
  }

}
