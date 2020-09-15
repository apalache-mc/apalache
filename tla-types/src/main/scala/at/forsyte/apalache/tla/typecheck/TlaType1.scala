package at.forsyte.apalache.tla.typecheck

import scala.collection.immutable.SortedMap

/**
  * Trait for a type in Type System 1 as specified in
  * <a href="https://github.com/informalsystems/apalache/blob/unstable/docs/adr/002adr-types.md">ADR-002</a>.
  */
sealed trait TlaType1 {
  /**
    * Compute the set of the names used in the type. These are names declared with either VarT1, or ConstT1.
    * @return the set of names that are used in the type.
    */
  def usedNames: Set[String]
}

/**
  * An integer type.
  */
case class IntT1() extends TlaType1 {
  override def toString: String = "Int"

  override def usedNames: Set[String] = Set.empty
}

/**
  * An real type.
  */
case class RealT1() extends TlaType1 {
  override def toString: String = "Real"

  override def usedNames: Set[String] = Set.empty
}

/**
  * A Boolean type.
  */
case class BoolT1() extends TlaType1 {
  override def toString: String = "Bool"

  override def usedNames: Set[String] = Set.empty
}

/**
  * The type of an uninterpreted string literal.
  */
case class StrT1() extends TlaType1 {
  override def toString: String = "Str"

  override def usedNames: Set[String] = Set.empty
}

/**
  * An uninterpreted type constant.
  *
  * @param name unique name of the constant type
  */
case class ConstT1(name: String) extends TlaType1 {
  override def toString: String = name

  override def usedNames: Set[String] = Set(name)
}

/**
  * A type variable.
  *
  * TODO: as we will have numerous type variables during type inference, use integers instead of strings.
  *
  * @param name a variable name that should be assigned a type
  */
case class VarT1(name: String) extends TlaType1 {
  override def toString: String = name

  override def usedNames: Set[String] = Set(name)
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

  override def usedNames: Set[String] = arg.usedNames ++ res.usedNames
}

/**
  * A set type.
  *
  * @param elem the type of the elements
  */
case class SetT1(elem: TlaType1) extends TlaType1 {
  override def toString: String = s"Set($elem)"

  override def usedNames: Set[String] = elem.usedNames
}

/**
  * A sequence type.
  *
  * @param elem the type of the elements.
  */
case class SeqT1(elem: TlaType1) extends TlaType1 {
  override def toString: String = s"Seq($elem)"

  override def usedNames: Set[String] = elem.usedNames
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

  override def usedNames: Set[String] = elems.foldLeft(Set[String]()) { (s, t) => s ++ t.usedNames }
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

  override def usedNames: Set[String] = fieldTypes.values.foldLeft(Set[String]()) { (s, t) => s ++ t.usedNames }
}

object SparseTupT1 {
  def apply(keysAndTypes: (Int, TlaType1)*): SparseTupT1 = {
    SparseTupT1(SortedMap(keysAndTypes :_*))
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

  override def usedNames: Set[String] = fieldTypes.values.foldLeft(Set[String]()) { (s, t) => s ++ t.usedNames }
}

object RecT1 {
  def apply(keysAndTypes: (String, TlaType1)*): RecT1 = {
    RecT1(SortedMap(keysAndTypes :_*))
  }
}

/**
  * An operator type.
  *
  * @param args the arguments' types
  * @param res the result type
  */
case class OperT1(args: Seq[TlaType1], res: TlaType1) extends TlaType1 {
  override def toString: String = {
    val argStrs = args.map(_.toString)
    "(%s) => %s".format(argStrs.mkString(", "), res.toString)
  }

  override def usedNames: Set[String] = res.usedNames ++ args.foldLeft(Set[String]()) { (s, t) => s ++ t.usedNames }
}