package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir._

import scala.annotation.tailrec
import scala.collection.immutable.SortedMap

/**
 * A substitution from type variables to types.
 *
 * The mapping is keyed by the *representative* variable of each equivalence class (the smallest index in the class).
 * The optional varToClass maps every variable (including non-representatives) to its representative.
 *
 * @param mapping
 *   a mapping from representative variable index to type.
 * @param precomputedVarToClass
 *   optional pre-computed map from every variable index to its representative. When absent it is assumed every key in
 *   `mapping` is its own representative (i.e. all classes are singletons).
 */
class Substitution(val mapping: Map[Int, TlaType1],
    precomputedVarToClass: Option[Map[Int, Int]] = None) {
  import Substitution.SUB_LIMIT

  // Map every variable to its representative. For singleton classes the representative equals the variable itself.
  private lazy val varToClass: Map[Int, Int] = precomputedVarToClass.getOrElse {
    mapping.keys.map(k => k -> k).toMap
  }

  /**
   * Expose the full set of variable numbers covered by this substitution (representatives + all class members). Used by
   * ConstraintSolver to maintain the boundVars index.
   */
  def allVarNums: Set[Int] = varToClass.keySet

  /**
   * Expose the var→representative map for TypeUnifier to reconstruct union-find state without copying EqClass objects.
   */
  private[types] def varToClassMap: Map[Int, Int] = varToClass

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
        // Path compression: follow var→var chains to the terminal type in a single pass.
        // This avoids needing multiple subRec iterations for chains like a→b→c→Int.
        @tailrec def resolve(n: Int, followed: Boolean): (TlaType1, Boolean) = {
          varToClass.get(n) match {
            case None => (VarT1(n), followed)
            case Some(repr) =>
              mapping(repr) match {
                case VarT1(n2) if n2 != n && varToClass.contains(n2) =>
                  resolve(n2, true)
                case result =>
                  (result, tp != result || followed)
              }
          }
        }
        resolve(no, false)

      case IntT1 | BoolT1 | RealT1 | StrT1 | ConstT1(_) =>
        (tp, false)

      case SetT1(elem) =>
        val (nelem, isChanged) = sub(elem)
        if (isChanged) (SetT1(nelem), true) else (tp, false)

      case SeqT1(elem) =>
        val (nelem, isChanged) = sub(elem)
        if (isChanged) (SeqT1(nelem), true) else (tp, false)

      case TupT1(elems @ _*) =>
        val (nelems, isChangedSeq) = elems.map(sub).unzip
        val isChanged = isChangedSeq.contains(true)
        if (isChanged) (TupT1(nelems: _*), true) else (tp, false)

      case SparseTupT1(fieldTypes) =>
        var anyChanged = false
        val newPairs = fieldTypes.map { case (k, v) =>
          val (nv, c) = sub(v)
          if (c) anyChanged = true
          k -> nv
        }
        if (anyChanged) (SparseTupT1(newPairs.to(SortedMap)), true) else (tp, false)

      case RecT1(fieldTypes) =>
        var anyChanged = false
        val newPairs = fieldTypes.map { case (k, v) =>
          val (nv, c) = sub(v)
          if (c) anyChanged = true
          k -> nv
        }
        if (anyChanged) (RecT1(newPairs.to(SortedMap)), true) else (tp, false)

      case FunT1(arg, res) =>
        val (narg, isChangedArg) = sub(arg)
        val (nres, isChangedRes) = sub(res)
        if (isChangedArg || isChangedRes) (FunT1(narg, nres), true) else (tp, false)

      case OperT1(args, res) =>
        val (nargs, isChangedArgs) = args.map(sub).unzip
        val (nres, isChangedRes) = sub(res)
        val isChanged = isChangedRes || isChangedArgs.contains(true)
        if (isChanged) (OperT1(nargs, nres), true) else (tp, false)

      case row @ RowT1(fieldTypes, other) =>
        var anyFieldChanged = false
        val newPairs = fieldTypes.map { case (k, v) =>
          val (nv, c) = sub(v)
          if (c) anyFieldChanged = true
          k -> nv
        }
        other match {
          case None =>
            if (!anyFieldChanged) (row, false)
            else (RowT1(newPairs.to(SortedMap), None), true)

          case Some(v) =>
            val (subv, isChangedVar) = sub(v)
            if (!anyFieldChanged && !isChangedVar) (row, false)
            else
              // nv is either a variable or a row
              subv match {
                case nv @ VarT1(_) =>
                  (RowT1(newPairs.to(SortedMap), Some(nv)), true)

                case RowT1(otherFieldTypes, otherVar) =>
                  (RowT1((otherFieldTypes ++ newPairs).to(SortedMap), otherVar), true)

                case other =>
                  throw new IllegalStateException("Expected a var or a row, found: " + other)
              }
        }

      case RecRowT1(row) =>
        val (newRow, rowChanged) = sub(row)
        if (!rowChanged) (tp, false)
        else
          newRow match {
            case r @ RowT1(_, _) =>
              (RecRowT1(r), true)

            case tt =>
              throw new IllegalStateException("Expected a row after substitution, found: " + tt)
          }

      case VariantT1(row) =>
        val (newRow, rowChanged) = sub(row)
        if (!rowChanged) (tp, false)
        else
          newRow match {
            case r @ RowT1(_, _) =>
              (VariantT1(r), true)

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
    var iterations = 0
    while (limit > 0) {
      val (newType, isChanged) = sub(intermediateType)
      iterations += 1
      if (!isChanged) {
        if (TypeCheckerProfiler.enabled) {
          TypeCheckerProfiler.subRecCallCount += 1
          TypeCheckerProfiler.subRecTotalIterations += iterations
          if (iterations > TypeCheckerProfiler.subRecMaxIterations) TypeCheckerProfiler.subRecMaxIterations = iterations
        }
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
    def clsStr(repr: Int): String = {
      val members = varToClass.filter(_._2 == repr).keys.toSeq.sorted
      if (members.size == 1) VarT1(repr).toString
      else members.map(VarT1(_).toString).mkString("{", ", ", "}")
    }
    "Sub{%s}".format(
        String.join(", ", mapping.toSeq.map(p => "[%s] -> %s".format(clsStr(p._1), p._2)): _*))
  }

  def canEqual(other: Any): Boolean = other.isInstanceOf[Substitution]

  // Comparison of two substitutions. Two substitutions are equal if they produce the same type for every variable:
  // same mapping keys/values AND same class memberships.
  override def equals(other: Any): Boolean = other match {
    case that: Substitution =>
      mapping == that.mapping && varToClass == that.varToClass

    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(mapping, varToClass)
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

  def apply(elems: (Int, TlaType1)*): Substitution = {
    new Substitution(Map(elems: _*))
  }

  def apply(context: Map[Int, TlaType1]): Substitution = {
    new Substitution(context)
  }

  /**
   * Compatibility factory: build a Substitution from EqClass-keyed pairs. Each EqClass's typeVars set determines which
   * variables are in the same equivalence class; the EqClass's reprVar is the representative (map key).
   *
   * This is used in tests that were written against the old EqClass-based API.
   */
  def fromEqClasses(elems: (EqClass, TlaType1)*): Substitution = {
    val mapping = elems.map { case (cls, tp) => cls.reprVar -> tp }.toMap
    val varToClass = elems.flatMap { case (cls, _) =>
      cls.typeVars.map(_ -> cls.reprVar)
    }.toMap
    new Substitution(mapping, Some(varToClass))
  }
}
