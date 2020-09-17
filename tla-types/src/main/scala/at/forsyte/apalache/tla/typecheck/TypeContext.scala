package at.forsyte.apalache.tla.typecheck

import scala.collection.immutable.SortedMap

/**
  * A type context assigns poly- or monotypes to names (such as operator names and the names of bound variables).
  *
  * @author
  */
class TypeContext(val types: Map[String, TlaType1]) {
  def apply(name: String): TlaType1 = {
    types(name)
  }

  /**
    * Substitute all names with poly- or monotypes.
    * @param tp a type that may contain free names.
    * @return a pair that consists of:
    *         (1) the new type where all names available in the context are replaced with the types, and
    *         (2) a Boolean flag of whether the substitution has left some names unresolved, that is,
    *         produced a parameterized type, not a monotype.
    */
  def sub(tp: TlaType1): (TlaType1, Boolean) = {
    def subList(elems: Iterable[TlaType1]): (Seq[TlaType1], Boolean) = {
      val subResult = elems map sub
      val existsParam = subResult.exists(_._2)
      (subResult.map(_._1).toSeq, existsParam)
    }

    tp match {
      case v @ VarT1(no) if types.contains(v.toString) => (types(v.toString), false)
      case VarT1(_) => (tp, true)

      case ConstT1(_) => (tp, false) // the constant type is never substituted

      case FunT1(arg, res) =>
        val (argSub, argParam) = sub(arg)
        val (resSub, resParam) = sub(res)
        (FunT1(argSub, resSub), argParam || resParam)

      case OperT1(args, res) =>
        val (subArgs, isParam) = subList(res +: args)
        (OperT1(subArgs.tail, subArgs.head), isParam)

      case SetT1(elem) =>
        val (subElem, isParam) = sub(elem)
        (SetT1(subElem), isParam)

      case SeqT1(elem) =>
        val (subElem, isParam) = sub(elem)
        (SeqT1(subElem), isParam)

      case TupT1(elems @ _*) =>
        val (subElems, isParam) = subList(elems)
        (TupT1(subElems :_*), isParam)

      case SparseTupT1(fieldTypes) =>
        val (subValues, isParam) = subList(fieldTypes.values)
        (SparseTupT1(SortedMap(fieldTypes.keys.zip(subValues).toSeq :_*)), isParam)

      case RecT1(fieldTypes) =>
        val (subValues, isParam) = subList(fieldTypes.values)
        (RecT1(SortedMap(fieldTypes.keys.zip(subValues).toSeq :_*)), isParam)

      case _ =>
        (tp, false)
    }
  }
}

object TypeContext {
  val empty: TypeContext = new TypeContext(Map.empty)

  def apply(namedTypes: (String, TlaType1)*): TypeContext = {
    new TypeContext(SortedMap(namedTypes :_*))
  }
}