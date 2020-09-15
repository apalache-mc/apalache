package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.typecheck._

/**
  * A substitution from type variables to types.
  * @param map a mapping from variable names to types.
  */
class Substitution(val map: Map[String, TlaType1]) {
  def apply(tp: TlaType1): TlaType1 = {
    tp match {
      case ConstT1(name) =>
        map.get(name) match {
          case Some(tt) => tt
          case None => tp
        }

      case VarT1(name) =>
        map.get(name) match {
          case Some(tt) => tt
          case None => tp
        }

      case SetT1(elem) =>
        SetT1(this(elem))

      case SeqT1(elem) =>
        SeqT1(this(elem))

      case TupT1(elems @ _*) =>
        TupT1(elems.map(this(_)) :_*)

      case SparseTupT1(fieldTypes) =>
        SparseTupT1(fieldTypes.map(kv => (kv._1, this(kv._2))))

      case RecT1(fieldTypes) =>
        RecT1(fieldTypes.map(kv => (kv._1, this(kv._2))))

      case FunT1(arg, res) =>
        FunT1(this(arg), this(res))

      case OperT1(args, res) =>
        OperT1(args.map(this(_)), this(res))

      case _ =>
        tp // Bool, Int, Real, Str
    }
  }

  override def toString: String = {
    "Sub{%s}".format(String.join(", ", map.toSeq.map(p => "%s -> %s".format(p._1, p._2)) :_*))
  }

  def canEqual(other: Any): Boolean = other.isInstanceOf[Substitution]

  override def equals(other: Any): Boolean = other match {
    case that: Substitution =>
      (that canEqual this) &&
        map == that.map
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(map)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}

object Substitution {
  val empty = new Substitution(Map.empty)

  def apply(elems: (String, TlaType1)*): Substitution = {
    new Substitution(Map(elems: _*))
  }

  def apply(map: Map[String, TlaType1]): Substitution = {
    new Substitution(map)
  }
}