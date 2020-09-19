package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.typecheck._

import scala.collection.immutable.SortedMap

/**
  * <p>A unification solver for the TlaType1 system. Note that our subtyping relation unifies records
  * and sparse tuples with a different number of fields. It does so by extending the key set, not by shrinking it.</p>
  *
  * <p>This class is not designed for concurrency. Use different instances in different threads.</p>
  *
  * @author Igor Konnov
  */
class TypeUnifier {
  // a partial solution to the unification problem is stored here during unification
  private var solution: Map[Int, TlaType1] = Map.empty

  def unify(substitution: Substitution, lhs: TlaType1, rhs: TlaType1): Option[(Substitution, TlaType1)] = {
    // start with the substitution
    solution = substitution.map
    // try to unify
    compute(lhs, rhs) match {
      case None => // no unifier
        None

      case Some(unifiedType) =>
        val result =
          if (isCyclic) {
            None
          } else {
            Some((new Substitution(solution), unifiedType))
          }

        solution = Map.empty // let GC collect the solution map later
        result
    }
  }

  def unify(substitution: Substitution, pairs: Seq[(TlaType1, TlaType1)]): Option[(Substitution, Seq[TlaType1])] = {
    // start with the substitution
    solution = substitution.map

    val unified = pairs.map { case (l, r) => compute(l, r) }
    val result =
      if (unified.forall(_.isDefined)) {
        Some((Substitution(solution), unified.map(_.get)))
      } else {
        None
      }

    solution = Map.empty // let GC collect the solution map later
    result
  }

  private def computeOptions(lhs: Option[TlaType1], rhs: Option[TlaType1]): Option[TlaType1] = {
    (lhs, rhs) match {
      case (Some(l), Some(r)) => compute(l, r)
      case (None, Some(r)) => Some(r)
      case (l @ _, None) => l // Some or None
    }
  }

  private def compute(lhs: TlaType1, rhs: TlaType1): Option[TlaType1] = {
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

        // variables contribute to the solutions
      case (lvar @ VarT1(lname), rvar @ VarT1(rname)) =>
        (solution.get(lname), solution.get(rname)) match {
          case (Some(lvalue), Some(rvalue)) =>
            if (insert(lname, rvalue) && insert(rname, lvalue)) {
              Some(solution(lname)) // both values unify
            } else {
              None  // a = b, but their values do not unify
            }

          case (Some(lvalue), None) =>
            insert(rname, lvalue) // None and lvalue for sure unify, associate lvalue with rname
            Some(lvalue)

          case (None, Some(rvalue)) =>
            insert(lname, rvalue) // None and rvalue for sure unify, associate rvalue with lname
            Some(rvalue)

          case (None, None) =>
            // assign one variable to another, while preserving the variable order
            if (lname > rname) {
              insert(lname, rvar) // b <- a, as in our type checking, b is more precise
              Some(rvar)
            } else if (lname < rname) {
              insert(rname, lvar) // b <- a
              Some(lvar)
            } else {
              // else it is the same variable, do nothing
              Some(lvar)
            }
        }

      case (VarT1(name), other) =>
        if (insert(name, other)) {
          Some(solution(name))
        } else {
          None
        }

      case (other, VarT1(name)) =>
        if (insert(name, other)) {
          Some(solution(name))
        } else {
          None
        }

        // functions should unify component-wise
      case (FunT1(larg, lres), FunT1(rarg, rres)) =>
        (compute(larg, rarg), compute(lres, rres)) match {
          case (Some(uarg), Some(ures)) => Some(FunT1(uarg, ures))
          case _ => None // no common unifier
        }

      // operators should unify component-wise
      case (OperT1(largs, lres), OperT1(rargs, rres)) =>
        unifySeqs(lres +: largs, rres +: rargs) match {
          case None =>
            None

          case Some(unified) =>
            Some(OperT1(unified.tail, unified.head))
        }

        // sets unify on their elements
      case (SetT1(lelem), SetT1(relem)) =>
        compute(lelem, relem) match {
          case None => None
          case Some(unified) => Some(SetT1(unified))
        }

        // sequences unify on their elements
      case (SeqT1(lelem), SeqT1(relem)) =>
        compute(lelem, relem) match {
          case None => None
          case Some(unified) => Some(SeqT1(unified))
        }

      // tuples unify component-wise
      case (TupT1(lelems @ _*), TupT1(relems @ _*)) =>
        unifySeqs(lelems, relems) match {
          case None => None
          case Some(unified) => Some(TupT1(unified :_*))
        }

      // sparse tuples join their keys, but the values for the intersecting keys should unify
      case (SparseTupT1(lfields), SparseTupT1(rfields)) =>
        val jointKeys = (lfields.keySet ++ rfields.keySet).toSeq
        val pairs = jointKeys.map(key => (key, computeOptions(lfields.get(key), rfields.get(key))))
        if (pairs.exists(_._2.isEmpty)) {
          None
        } else {
          val unifiedTuple = SparseTupT1(SortedMap(pairs.map(p => (p._1, p._2.get)) :_*))
          Some(unifiedTuple)
        }

        // sparse tuples consume tuples
      case (l @ SparseTupT1(_), TupT1(relems @ _*)) =>
        compute(l, SparseTupT1(SortedMap(relems.zipWithIndex.map(p => (p._2, p._1)) :_*)))

        // sparse tuples consume tuples
      case (l @ TupT1(_), r @ SparseTupT1(_)) =>
        compute(r, l)

        // records join their keys, but the values for the intersecting keys should unify
      case (RecT1(lfields), RecT1(rfields)) =>
        val jointKeys = (lfields.keySet ++ rfields.keySet).toSeq
        val pairs = jointKeys.map(key => (key, computeOptions(lfields.get(key), rfields.get(key))))
        if (pairs.exists(_._2.isEmpty)) {
          None
        } else {
          val unifiedTuple = RecT1(SortedMap(pairs.map(p => (p._1, p._2.get)) :_*))
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
      None        // different number of arguments
    } else {
      val unified = ls.zip(rs).map { case (l, r) => compute(l, r) }
      if (unified.exists(_.isEmpty)) {
        None      // no unifier for at least one pair
      } else {
        Some(unified.map(_.get))    // all pairs unified
      }
    }
  }

  // insert a type into the substitution, by applying unification
  private def insert(key: Int, tp: TlaType1): Boolean = {
    solution.get(key) match {
      case None =>
        solution += key -> tp // associate the type with the key
        true

      case Some(other) =>
        compute(tp, other) match {
          case None =>
            false // insertion failed

          case Some(unifiedType) =>
            solution += key -> unifiedType // unified two values
            true
        }

    }
  }

  // Check, whether the solution is cyclic.
  // This solution is computing the greatest fix-point, so it probably not the most optimal.
  // However, our substitutions in the type checker are quite small.
  private def isCyclic: Boolean = {
    // successors for every variable
    val succ = solution.mapValues(_.usedNames)
    var prev = Set[Int]()
    var next = succ.keySet
    // compute the greatest fixpoint under the successor function
    while (prev != next) {
      prev = next
      next = next.foldLeft(Set[Int]()) { case (s, i) => s ++ succ.getOrElse(i, Set.empty) }
    }

    // if the fix-point is empty, there is no cycle
    next.nonEmpty
  }
}
