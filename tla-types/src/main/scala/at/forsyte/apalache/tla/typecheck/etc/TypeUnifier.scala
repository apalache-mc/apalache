package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir._

import scala.collection.immutable.SortedMap

/**
 * <p>A unification solver for the TlaType1 system. Note that our subtyping relation unifies records
 * and sparse tuples with a different number of fields. It does so by extending the key set, not by shrinking it.
 * </p>
 *
 * <p>For an explanation of unification, see a textbook on logic, e.g.,
 * Melvin Fitting. First-Order Logic and Automated Theorem Proving, Springer, 1996.
 * We adapted the classical unification to reason about equivalence classes of type variables.
 * We have focused on soundness of type unification. So this class may have poor performance when called by the
 * constraint solver multiple times. Some profiling is needed.
 * </p>
 *
 * <p>This class is not designed for concurrency. Use different instances in different threads.</p>
 *
 * @author Igor Konnov
 */
class TypeUnifier {
  // A variable is mapped to its equivalence class. By default, a variable sits in the singleton equivalence class
  // of its own. When two variables are unified, they are merged in the same equivalence class.
  private var varToClass: Map[Int, EqClass] = Map.empty
  // A partial solution to the unification problem is stored here during unification.
  // Importantly, instead of mapping a variable to a type, we map an equivalence class to a type.
  // By doing so, we make sure that equivalent variables are mapped to the same type.
  private var solution: Map[EqClass, TlaType1] = Map.empty

  /**
   * Try to unify lhs and rhs by starting with the given substitution. If successful, it returns Some(mgu, t),
   * where mgu is the solution set showing how to unify lhs and rhs and t is the type resulting from
   * successfully unifying lhs and rhs using mgu. Note that apart from variable substitution, our unification
   * also involves merging record types. When there is no unifier, it returns None.
   */
  def unify(substitution: Substitution, lhs: TlaType1, rhs: TlaType1): Option[(Substitution, TlaType1)] = {
    // Copy the equivalence classes and the mapping from the substitution.
    // It is important to introduce fresh copies of the classes, as they may be merged in the unification process.
    solution = Map.empty
    varToClass = Map.empty
    var usedVars = lhs.usedNames ++ rhs.usedNames
    for ((cls, tp) <- substitution.mapping) {
      val copy = cls.copy()
      solution += copy -> tp
      varToClass ++= copy.typeVars.map(_ -> copy)
      usedVars ++= tp.usedNames
    }

    // Introduce an equivalence class for every used variable that does not have a class assigned yet.
    // This simplifies the algorithm, as we don't have to check, whether a variable has been assigned a class.
    for (v <- usedVars) {
      if (!varToClass.contains(v)) {
        val cls = EqClass(v)
        varToClass += v -> cls
        // point to the variable itself
        solution += cls -> VarT1(v)
      }
    }

    // try to unify
    val result =
      compute(lhs, rhs) flatMap { unifiedType =>
        // use only the representative variables of every equivalence class
        val canonical = mkCanonicalSub
        val substitution = new Substitution(solution.mapValues { tt => canonical.sub(tt)._1 })
        Some((substitution, substitution.sub(unifiedType)._1))
      }
    // help GC to clean up later
    solution = Map.empty
    varToClass = Map.empty
    result
  }

  // Compute the unification of the value corresponding to the key in the two maps of fields
  private def computeFields[K](key: K, lhsFields: SortedMap[K, TlaType1],
      rhsFields: SortedMap[K, TlaType1]): Option[TlaType1] = {
    (lhsFields.get(key), rhsFields.get(key)) match {
      case (None, None)       => None
      case (Some(l), Some(r)) => compute(l, r)
      // Unifying a present field with an absent one is solved by the present one, as per
      // the typing rules on records that allows records with non-overlapping fields to
      // be values of the same type.
      case (None, r @ Some(_)) => r
      case (l @ Some(_), None) => l
    }
  }

  private def compute(lhs: TlaType1, rhs: TlaType1): Option[TlaType1] = {
    // Try to unify a variable with a non-variable term `typeTerm`.
    // If `typeTerm` refers to a variable in the equivalence class of `typeVar`, then this is a cyclic reference,
    // and there should be no unifier.
    def unifyVarWithNonVarTerm(typeVar: Int, typeTerm: TlaType1): Option[TlaType1] = {
      // Note that `typeTerm` is not a variable.
      val varClass = varToClass(typeVar)
      if (doesUseClass(typeTerm, varClass)) {
        // No unifier: `typeTerm` refers to a variable in the equivalence class of `typeVar`.
        None
      } else {
        // this variable is associated with an equivalence class, unify the class with `typeTerm`
        solution(varClass) match {
          case VarT1(_) =>
            // an equivalence class of free variables, just assign `typeTerm` to this class
            solution += varClass -> typeTerm
            Some(typeTerm)

          case _ =>
            // unify `typeTerm` with the term assigned to the equivalence class, if possible
            val unifier = compute(solution(varClass), typeTerm)
            unifier.foreach { t => solution += varClass -> t }
            unifier
        }
      }
    }

    // unify types as terms
    (lhs, rhs) match {
      // unifying constant types is trivial
      case (BoolT1(), BoolT1()) =>
        Some(BoolT1())

      case (IntT1(), IntT1()) =>
        Some(IntT1())

      case (StrT1(), StrT1()) =>
        Some(StrT1())

      case (RealT1(), RealT1()) =>
        Some(RealT1())

      case (c @ ConstT1(lname), ConstT1(rname)) =>
        // uninterpreted constant types must have the same name
        if (lname != rname) None else Some(c)

      case (VarT1(lname), VarT1(rname)) =>
        if (lname != rname) {
          mergeClasses(lname, rname)
        } else {
          Some(VarT1(lname))
        }

      case (VarT1(name), other) =>
        unifyVarWithNonVarTerm(name, other)

      case (other, VarT1(name)) =>
        unifyVarWithNonVarTerm(name, other)

      // functions should unify component-wise
      case (FunT1(larg, lres), FunT1(rarg, rres)) =>
        (compute(larg, rarg), compute(lres, rres)) match {
          case (Some(uarg), Some(ures)) => Some(FunT1(uarg, ures))
          case _                        => None // no common unifier
        }

      // operators should unify component-wise
      case (OperT1(largs, lres), OperT1(rargs, rres)) =>
        unifySeqs(lres +: largs, rres +: rargs).map(unified => OperT1(unified.tail, unified.head))

      // sets unify on their elements
      case (SetT1(lelem), SetT1(relem)) =>
        compute(lelem, relem).map(SetT1)

      // sequences unify on their elements
      case (SeqT1(lelem), SeqT1(relem)) =>
        compute(lelem, relem).map(SeqT1)

      // tuples unify component-wise
      case (TupT1(lelems @ _*), TupT1(relems @ _*)) =>
        unifySeqs(lelems, relems).map(unified => TupT1(unified: _*))

      // sparse tuples join their keys, but the values for the intersecting keys should unify
      case (SparseTupT1(lfields), SparseTupT1(rfields)) =>
        val jointKeys = (lfields.keySet ++ rfields.keySet).toSeq
        val pairs = jointKeys.map(key => (key, computeFields(key, lfields, rfields)))
        if (pairs.exists(_._2.isEmpty)) {
          None
        } else {
          val unifiedTuple = SparseTupT1(SortedMap(pairs.map(p => (p._1, p._2.get)): _*))
          Some(unifiedTuple)
        }

      // a sparse tuple is consumed by a tuple
      case (l @ SparseTupT1(_), TupT1(relems @ _*)) =>
        val nelems = relems.length
        if (l.fieldTypes.keySet.exists(i => i < 1 || i > nelems)) {
          // the sparse tuple is not allowed to have indices outside of the tuple domain
          None
        } else {
          // remember that tuples indices are starting with 1, not 0
          compute(l, SparseTupT1(SortedMap(relems.zipWithIndex.map(p => (1 + p._2, p._1)): _*))) match {
            case Some(SparseTupT1(fieldTypes)) =>
              // turn the total sparse tuple into a tuple
              Some(TupT1(1.to(relems.length).map(fieldTypes): _*))

            case _ => None // no unifier as sparse tuples
          }
        }

      // a sparse tuple is consumed by a tuple
      case (l @ TupT1(_ @_*), r @ SparseTupT1(_)) =>
        compute(r, l)

      // records join their keys, but the values for the intersecting keys should unify
      case (RecT1(lfields), RecT1(rfields)) =>
        val jointKeys = (lfields.keySet ++ rfields.keySet).toSeq
        val pairs = jointKeys.map(key => (key, computeFields(key, lfields, rfields)))
        if (pairs.exists(_._2.isEmpty)) {
          None
        } else {
          val unifiedTuple = RecT1(SortedMap(pairs.map(p => (p._1, p._2.get)): _*))
          Some(unifiedTuple)
        }

      // everything else does not unify
      case _ =>
        None // no unifier
    }
  }

  // unify two sequences
  private def unifySeqs(ls: Seq[TlaType1], rs: Seq[TlaType1]): Option[Seq[TlaType1]] = {
    val len = ls.length
    if (len != rs.length) {
      None // different number of arguments
    } else {
      val unified = ls.zip(rs).map { case (l, r) => compute(l, r) }
      if (unified.exists(_.isEmpty)) {
        None // no unifier for at least one pair
      } else {
        Some(unified.map(_.get)) // all pairs unified
      }
    }
  }

  // merge two equivalence classes of two variables, if possible
  private def mergeClasses(lvar: Int, rvar: Int): Option[TlaType1] = {
    // merge two equivalence classes, if possible
    val lcls = varToClass(lvar)
    val rcls = varToClass(rvar)
    if (lcls == rcls) {
      // always pick the variable with the minimal index as the representative
      Some(VarT1(lcls.reprVar))
    } else {
      // try to merge the classes
      val lterm = solution(lcls)
      val rterm = solution(rcls)
      lcls.typeVars ++= rcls.typeVars
      // Move the variables of the right class to the left class and remove the right class.
      // This is safe, because terms never access the classes directly, but refer to them via variables.
      rcls.typeVars foreach { v => varToClass += v -> lcls }
      solution -= rcls
      // if the assigned terms unify, add the unifier as a solution
      val unified = compute(lterm, rterm)
      unified.foreach { u => solution += lcls -> u }
      unified
    }
  }

  // Compute the transitive closure of the variables that are used by `tt` and their values that are known from the solution.
  private def doesUseClass(tt: TlaType1, lookFor: EqClass): Boolean = {
    def varsToClasses(vars: Set[Int]): Set[EqClass] = {
      vars.map(varToClass)
    }

    // look for equivalence classes by simple depth-first search
    var visited: Set[EqClass] = Set.empty
    var toVisit = varsToClasses(tt.usedNames)
    while (toVisit.nonEmpty) {
      val cls = toVisit.head
      if (cls == lookFor) {
        // found an occurrence of `lookFor`, return immediately
        return true
      }
      visited += cls
      toVisit -= cls
      val used = varsToClasses(solution(cls).usedNames)
      toVisit ++= used -- visited
    }

    false
  }

  // produce a canonical substitution
  // that replaces every variable of an equivalence class with the largest variable in the class
  private def mkCanonicalSub: Substitution = {
    val mapping = solution.keys.toSeq.map { cls =>
      (cls, VarT1(cls.reprVar))
    }
    new Substitution(Map[EqClass, TlaType1](mapping: _*))
  }
}

object TypeUnifier {
  class CycleDetected extends RuntimeException
}
