package at.forsyte.apalache.tla.lir

import scala.collection.immutable.SortedMap

/**
 * Trait for a type in Type System 1 as specified in <a
 * href="https://github.com/apalache-mc/apalache/blob/main/docs/src/adr/002adr-types.md">ADR-002</a>.
 *
 * It also contains experimental extensions that are specified in <a
 * href="https://github.com/apalache-mc/apalache/blob/main/docs/src/adr/014adr-precise-records.md">ADR-014</a>.
 */
sealed trait TlaType1 {

  /**
   * Compute the set of the names used in the type. These are names declared with VarT1.
   *
   * @return
   *   the set of variable names (actually, integers) that are used in the type.
   */
  def usedNames: Set[Int]

  def isMono: Boolean = TlaType1.isMono(this)
}

/**
 * A type signature of a let definition after the definition by Damas and Milner.
 *
 * @param principalType
 *   the parametric type of a definition, often called the principal type
 * @param quantifiedVars
 *   a subset of the variables used in `signature` that must be instantiated upon use.
 */
case class TlaType1Scheme(principalType: TlaType1, quantifiedVars: Set[Int])

object TlaType1 {
  def fromTypeTag(typeTag: TypeTag): TlaType1 = {
    typeTag match {
      case Typed(tt: TlaType1) => tt
      case _ => throw new TypingException("Expected Typed(_: TlaType1), found: " + typeTag, UID.nullId)
    }
  }

  // returns true iff the type is a monotype, i.e. if it contains no type variables
  def isMono(tt: TlaType1): Boolean = tt match {
    case IntT1 | RealT1 | BoolT1 | StrT1 | ConstT1(_) => true
    case _: VarT1                                     => false
    case FunT1(arg, res)                              => isMono(arg) && isMono(res)
    case SetT1(elem)                                  => isMono(elem)
    case SeqT1(elem)                                  => isMono(elem)
    case TupT1(elems @ _*)                            => elems.forall(isMono)
    case SparseTupT1(fieldTypes)                      => fieldTypes.values.forall(isMono)
    case RecT1(fieldTypes)                            => fieldTypes.values.forall(isMono)
    case OperT1(args, res)                            => (res +: args).forall(isMono)
    case RowT1(fieldTypes, other)                     => (other ++ fieldTypes.values).forall(isMono)
    case RecRowT1(row)                                => isMono(row)
    case VariantT1(row)                               => isMono(row)
  }
}

/**
 * An integer type.
 */
case object IntT1 extends TlaType1 {
  override def toString: String = "Int"

  override def usedNames: Set[Int] = Set.empty

}

/**
 * An real type.
 */
case object RealT1 extends TlaType1 {
  override def toString: String = "Real"

  override def usedNames: Set[Int] = Set.empty

}

/**
 * A Boolean type.
 */
case object BoolT1 extends TlaType1 {
  override def toString: String = "Bool"

  override def usedNames: Set[Int] = Set.empty

}

/**
 * The type of an uninterpreted string literal.
 */
case object StrT1 extends TlaType1 {
  override def toString: String = "Str"

  override def usedNames: Set[Int] = Set.empty

}

/**
 * An uninterpreted type constant such as `PROC_NAME`.
 *
 * Inside the type checker, this class may also represent references to type aliases. Do not use this feature outside of
 * the type checker.
 *
 * @param name
 *   unique name of the constant type
 */
case class ConstT1(name: String) extends TlaType1 {
  require(ConstT1.isUninterpreted(name) || ConstT1.isAliasReference(name),
      "ConstT1 accepts identifiers in upper case or $aliasReference, found: " + name)

  override def toString: String = name

  override def usedNames: Set[Int] = Set.empty
}

/**
 * A companion object for [[ConstT1]].
 */
object ConstT1 {
  // the regular expression that recognizes uninterpreted types
  private val uninterpretedRegex = "[A-Z_][A-Z0-9_]*".r

  /**
   * Does this type represent an uninterpreted type, e.g., PROCESS. Outside of the type parser and the type checker,
   * this method should always return true.
   *
   * @param name
   *   type name
   * @return
   *   true iff the type name represents an uninterpreted type.
   */
  def isUninterpreted(name: String): Boolean = {
    uninterpretedRegex.matches(name)
  }

  /**
   * Does this type represent a reference to an alias, e.g., `\$aliasReference`. This case is only of relevance to the
   * type parser and the type checker.
   *
   * @param name
   *   type name
   * @return
   *   true iff the type name represents a reference to an alias.
   */
  def isAliasReference(name: String): Boolean = {
    name.startsWith("$")
  }

  /**
   * Extract alias name from the reference syntax.
   *
   * @param reference
   *   a reference such as \$aliasRef
   * @return
   *   the name without the dollar sign
   */
  def aliasNameFromReference(reference: String): String = {
    if (reference.startsWith("$")) {
      reference.substring(1)
    } else {
      throw new IllegalArgumentException(s"Expected $reference to start with the dollar sign")
    }
  }
}

/**
 * A type variable. Instead of using strings for names, we are just using integers, which makes it easier to process
 * them. To make vars user-friendly, we assign the names a..z to the numbers `0..25`. The rest are called `a27`, `a28`,
 * etc.
 *
 * @param no
 *   the variable number
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
  protected val QNAMES: Vector[String] = Vector(
      "a",
      "b",
      "c",
      "d",
      "e",
      "f",
      "g",
      "h",
      "i",
      "j",
      "k",
      "l",
      "m",
      "n",
      "o",
      "p",
      "q",
      "r",
      "s",
      "t",
      "u",
      "v",
      "w",
      "x",
      "y",
      "z",
  )

  /**
   * Construct a variable from the human-readable form like `b` or `a100`. We use this method to write human-readable
   * variable names in tests.
   *
   * @param name
   *   a human-readable name
   * @return
   *   the variable that matches to that name
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
   * Call [[parse]] on `text`.
   *
   * @param text
   *   a string representation of a variable
   * @return
   *   the variable, if text is in the right format. Otherwise, throw IllegalArgumentException.
   */
  def apply(text: String): VarT1 = {
    parse(text)
  }

  /**
   * Is the provided string a valid variable name
   *
   * @param text
   *   a string
   * @return
   *   true if `text` is a valid variable name
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
 * @param arg
 *   the type of the argument; multiple arguments should be written as a tuple
 * @param res
 *   the type of the result
 */
case class FunT1(arg: TlaType1, res: TlaType1) extends TlaType1 {
  // always wrap a function with parenthesis, to make it non-ambiguous
  override def toString: String = s"($arg -> $res)"

  override def usedNames: Set[Int] = arg.usedNames ++ res.usedNames

}

/**
 * A set type.
 *
 * @param elem
 *   the type of the elements
 */
case class SetT1(elem: TlaType1) extends TlaType1 {
  override def toString: String = s"Set($elem)"

  override def usedNames: Set[Int] = elem.usedNames

}

/**
 * A sequence type.
 *
 * @param elem
 *   the type of the elements.
 */
case class SeqT1(elem: TlaType1) extends TlaType1 {
  override def toString: String = s"Seq($elem)"

  override def usedNames: Set[Int] = elem.usedNames

}

/**
 * A tuple type.
 *
 * @param elems
 *   a sequence of the element types
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
 * @param fieldTypes
 *   a sorted map from field names to their types
 */
case class SparseTupT1(fieldTypes: SortedMap[Int, TlaType1]) extends TlaType1 {
  override def toString: String = {
    val keyTypeStrs = fieldTypes.map(p => "%s: %s".format(p._1, p._2))
    "<| %s |>".format(keyTypeStrs.mkString(", "))
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
 * @param fieldTypes
 *   a sorted map from field names to their types
 *
 * @deprecated
 *   This type is superseded by RecRowT1 defined in ADR-014. It is kept only for backward compatibility. This type will
 *   be removed in future versions.
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
 * @param args
 *   the arguments' types
 * @param res
 *   the result type
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

/**
 * ****************** EXTENSIONS OF ADR014 ******************************
 */

/**
 * A row type that contains a collection of fields with assigned types and an optional variable that represents the part
 * to be defined.
 *
 * @param fieldTypes
 *   a mapping from field names to field types, which may be parameterized
 * @param other
 *   the undefined part: Either None, or Some(variable)
 */
case class RowT1(fieldTypes: SortedMap[String, TlaType1], other: Option[VarT1]) extends TlaType1 {
  override def toString: String = {
    val pairs = fieldTypes.map(p => "%s: %s".format(p._1, p._2)).mkString(" | ")
    other match {
      case None    => if (pairs.nonEmpty) s"(| $pairs |)" else "(||)"
      case Some(v) => if (pairs.nonEmpty) s"(| $pairs | $v |)" else s"(| $v |)"
    }
  }

  override def usedNames: Set[Int] =
    fieldTypes.values
      .map(_.usedNames)
      .foldLeft(other.map(_.usedNames).getOrElse(Set.empty))(_ ++ _)
}

object RowT1 {
  def apply(fieldTypes: (String, TlaType1)*): RowT1 = {
    RowT1(SortedMap(fieldTypes: _*), None)
  }

  def apply(other: VarT1, fieldTypes: (String, TlaType1)*): RowT1 = {
    RowT1(SortedMap(fieldTypes: _*), Some(other))
  }
}

/**
 * A record constructed from a row type. That the row is of the right kind should be checked by the kind unifier.
 *
 * @param row
 *   a row that is closed with this record
 */
case class RecRowT1(row: RowT1) extends TlaType1 {
  override def toString: String = {
    // the special user-friendly form, e.g., { foo: Int, g: Bool } or { foo: Int, g: Bool, a }
    val fields = row.fieldTypes.map(p => "%s: %s".format(p._1, p._2)).mkString(", ")
    row.other match {
      case None    => s"{ $fields }"
      case Some(v) => if (fields.nonEmpty) s"{ $fields, $v }" else s"{ $v }"
    }

  }

  override def usedNames: Set[Int] = row.usedNames
}

/**
 * A variant constructed from a row type. That the row is of the right kind should be checked by the kind unifier.
 *
 * @param row
 *   a row that is closed with the variant
 */
case class VariantT1(row: RowT1) extends TlaType1 {
  override def toString: String = {
    // the special user-friendly form, e.g.,
    // tag1(a) | tag2(b), or
    // tag1(a) | tag2(b) | c
    val options = row.fieldTypes
      .map { case (tag, tp) =>
        s"$tag($tp)"
      }
      .mkString(" | ")
    row.other match {
      case None    => options
      case Some(v) => if (options.nonEmpty) s"$options | $v" else s"Variant($v)"
    }
  }

  override def usedNames: Set[Int] = row.usedNames
}
