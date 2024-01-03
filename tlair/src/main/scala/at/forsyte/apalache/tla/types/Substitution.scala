package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir._

import scala.collection.immutable.SortedMap

/**
 * A substitution from type variables to types.
 *
 * @param mapping
 *   a mapping from variable names to types.
 */
class Substitution(val mapping: Map[EqClass, TlaType1]) {
  import Substitution.SUB_LIMIT
  // map every variable to its equivalence class (assuming that the classes are disjoint)
  private lazy val varToClass = mapping.keys.foldLeft(Map[Int, EqClass]()) { (map, cls) =>
    map ++ cls.typeVars.map(_ -> cls)
  }

  /**
   * Substitute variables with the types that are assigned in the context. Importantly, the substitution is applied only
   * once.
   *
   * @param tp
   *   a type term
   * @return
   *   the type term in which the variables have been substituted and whether any substitution has happened
   */
  def sub(tp: TlaType1): (TlaType1, Boolean) = {
    tp match {
      case VarT1(no) =>
        if (varToClass.contains(no)) {
          val result = mapping(varToClass(no))
          (result, tp != result)
        } else {
          (tp, false)
        }

      case IntT1 | BoolT1 | RealT1 | StrT1 | ConstT1(_) =>
        (tp, false)

      case SetT1(elem) =>
        val (nelem, isChanged) = sub(elem)
        (SetT1(nelem), isChanged)

      case SeqT1(elem) =>
        val (nelem, isChanged) = sub(elem)
        (SeqT1(nelem), isChanged)

      case TupT1(elems @ _*) =>
        val (nelems, isChanged) = elems.map(sub).unzip
        (TupT1(nelems: _*), isChanged.contains(true))

      case SparseTupT1(fieldTypes) =>
        val ntypesAndChanged = fieldTypes.map(kv => (kv._1, sub(kv._2)))
        val ntypes = ntypesAndChanged.view.mapValues(_._1).toMap.to(SortedMap)
        val isChanged = ntypesAndChanged.exists(_._2._2)
        (SparseTupT1(ntypes), isChanged)

      case RecT1(fieldTypes) =>
        val ntypesAndChanged = fieldTypes.map(kv => (kv._1, sub(kv._2)))
        val ntypes = ntypesAndChanged.view.mapValues(_._1).toMap.to(SortedMap)
        val isChanged = ntypesAndChanged.exists(_._2._2)
        (RecT1(ntypes), isChanged)

      case FunT1(arg, res) =>
        val (narg, isChangedArg) = sub(arg)
        val (nres, isChangedRes) = sub(res)
        (FunT1(narg, nres), isChangedArg || isChangedRes)

      case OperT1(args, res) =>
        val (nargs, isChangedArgs) = args.map(sub).unzip
        val (nres, isChangedRes) = sub(res)
        (OperT1(nargs, nres), isChangedRes || isChangedArgs.contains(true))

      case RowT1(fieldTypes, other) =>
        val (ntypes, isChangedFields) = fieldTypes.values.toSeq.map(sub).unzip
        val nfieldTypes = fieldTypes.keys.zip(ntypes).toSeq
        val hasChangedField = isChangedFields.contains(true)
        other match {
          case None =>
            (RowT1(nfieldTypes: _*), hasChangedField)

          case Some(v) =>
            val (subv, isChangedVar) = sub(v)
            // nv is either a variable or a row
            subv match {
              case nv @ VarT1(_) =>
                (RowT1(nv, nfieldTypes: _*), isChangedVar || hasChangedField)

              case RowT1(otherFieldTypes, otherVar) =>
                (RowT1(otherFieldTypes ++ nfieldTypes, otherVar), isChangedVar || hasChangedField)

              case tp =>
                throw new IllegalStateException("Expected a var or a row, found: " + tp)
            }
        }

      case RecRowT1(row) =>
        val (newRow, rowChanged) = sub(row)
        newRow match {
          case r @ RowT1(_, _) =>
            (RecRowT1(r), rowChanged)

          case tt =>
            throw new IllegalStateException("Expected a row after substitution, found: " + tt)
        }

      case VariantT1(row) =>
        val (newRow, rowChanged) = sub(row)
        newRow match {
          case r @ RowT1(_, _) =>
            (VariantT1(r), rowChanged)

          case tt =>
            throw new IllegalStateException("Expected a row after substitution, found: " + tt)
        }
    }
  }

  /**
   * Recursively substitute variables with the types that are assigned in the context. This substitution applies until
   * it converges, assuming that the substitution is acyclic.
   *
   * @param tp
   *   a type term
   * @return
   *   the type term in which the variables have been substituted
   */
  def subRec(tp: TlaType1): TlaType1 = {
    var limit = SUB_LIMIT
    var intermediateType = tp
    while (limit > 0) {
      val (newType, isChanged) = sub(intermediateType)
      if (!isChanged) {
        return newType
      } else {
        intermediateType = newType
      }
      limit -= 1
    }

    throw new IllegalStateException(
        s"Recursive substitution took more than $SUB_LIMIT iterations. Broken substitution?")
  }

  /**
   * Is the substitution defined over the empty domain?
   *
   * @return
   *   true if the substitution domain is empty
   */
  def isEmpty: Boolean = {
    mapping.isEmpty
  }

  override def toString: String = {
    def cls(c: EqClass): String = c.typeVars.map(VarT1(_).toString).mkString(", ")

    "Sub{%s}".format(String.join(", ", mapping.toSeq.map(p => "[%s] -> %s".format(cls(p._1), p._2)): _*))
  }

  def canEqual(other: Any): Boolean = other.isInstanceOf[Substitution]

  // Comparison of two substitutions is expensive, but we mainly use it for testing.
  // We use structural equality of equivalence classes instead of shallow comparison by ids.
  override def equals(other: Any): Boolean = other match {
    case that: Substitution =>
      (mapping.size == that.mapping.size) && mapping.forall { case (lcls, ltype) =>
        that.mapping.exists { case (rcls, rtype) =>
          lcls.deepEquals(rcls) && ltype == rtype
        }
      }

    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(mapping)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}

object Substitution {

  /**
   * The limit on the number of recursive substitutions (to avoid infinite cycles).
   */
  val SUB_LIMIT = 100000

  /**
   * An empty substitution.
   */
  val empty = new Substitution(Map.empty)

  def apply(elems: (EqClass, TlaType1)*): Substitution = {
    new Substitution(Map(elems: _*))
  }

  def apply(context: Map[EqClass, TlaType1]): Substitution = {
    new Substitution(context)
  }
}
