package at.forsyte.apalache.tla.typecheck

import scala.collection.immutable.SortedMap

/**
  * Trait for a type in Type System 1 as specified in
  * <a href="https://github.com/informalsystems/apalache/blob/unstable/docs/adr/002adr-types.md">ADR-002</a>.
  */
sealed trait TlaType1

/**
  * An integer type.
  */
case class IntT1() extends TlaType1 {
  override def toString: String = "Int"
}

/**
  * A Boolean type.
  */
case class BoolT1() extends TlaType1 {
  override def toString: String = "Bool"
}

/**
  * The type of an uninterpreted string literal.
  */
case class StrT1() extends TlaType1 {
  override def toString: String = "Str"
}

/**
  * An uninterpreted type constant.
  *
  * @param name unique name of the constant type
  */
case class ConstT1(name: String) extends TlaType1 {
  override def toString: String = name
}

/**
  * A type variable.
  *
  * @param name a variable name that should be assigned a type
  */
case class VarT1(name: String) extends TlaType1 {
  override def toString: String = name
}

/**
  * A function type.
  *
  * @param arg the type of the argument; multiple arguments should be written as a tuple
  * @param res the type of the result
  */
case class FunT1(arg: TlaType1, res: TlaType1) extends TlaType1 {
  override def toString: String = s"$arg -> $res"
}

/**
  * A set type.
  *
  * @param elem the type of the elements
  */
case class SetT1(elem: TlaType1) extends TlaType1 {
  override def toString: String = s"Set($elem)"
}

/**
  * A sequence type.
  *
  * @param elem the type of the elements.
  */
case class SeqT1(elem: TlaType1) extends TlaType1 {
  override def toString: String = s"Seq($elem)"
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
}