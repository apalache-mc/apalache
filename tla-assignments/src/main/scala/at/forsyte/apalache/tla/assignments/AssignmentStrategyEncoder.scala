package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.smt.SmtTools

import scala.collection.immutable.{Map, Set}

object AssignmentStrategyEncoder {

  /**
   * Collection of aliases used in internal methods.
   */
  type seenType = Set[Long]
  type collocSetType = Set[(Long, Long)]
  type nonCollocSetType = collocSetType
  type deltaType = Map[String, SmtTools.BoolFormula]
  type frozenVarSetType = Set[String]
  type frozenType = Map[Long, frozenVarSetType]
  type uidToExMapType = Map[Long, TlaEx]

  sealed case class StaticAnalysisData(
      seen: seenType, collocSet: collocSetType, nonCollocSet: nonCollocSetType, delta: deltaType, frozen: frozenType,
      uidToExmap: uidToExMapType
  ) {
    def simplified: StaticAnalysisData = this.copy(
        delta = delta.map { case (k, v) => (k, SmtTools.simplify(v)) }
    )
  }

  type letInOperBodyMapType = Map[String, StaticAnalysisData]
}

/**
 * Generates SMT constraints for assignment strategies.
 *
 * Assumes input is alpha-TLA+
 */
class AssignmentStrategyEncoder(val m_varSym: String = "b", val m_fnSym: String = "R") {

  import SmtTools._
  import AssignmentStrategyEncoder._

  /**
   * Main internal method.
   * *
   * @param phi Input formula
   * @param vars Set of all variables, domain of delta.
   * @param initialFrozenVarSet Variables, which are known to be frozen (i.e., free variables defining
   *                       a bound variable or IF-condition of an ancestor).
   * @return The tuple (S, C, nC, d, f), where S is the set of visited leaves,
   *         C is the (partial) collocation set,
   *         nC is the (partial) no-collocation set,
   *         d is the (partial) delta function
   *         and f is the (partial) frozen function.
   */
  private[assignments] def staticAnalysis(
      phi: TlaEx, vars: Set[String], initialFrozenVarSet: frozenVarSetType,
      initialLetInOperBodyMap: letInOperBodyMapType, manuallyAssigned: Set[String]
  ): StaticAnalysisData = {
    import AlphaTLApTools._

    /** We name the default arguments to return at irrelevant terms */
    val defaultArgs: StaticAnalysisData =
      StaticAnalysisData(
          seen = Set.empty[Long],
          collocSet = Set.empty[(Long, Long)],
          nonCollocSet = Set.empty[(Long, Long)],
          delta = (vars map { v => (v, False()) }).toMap,
          frozen = Map.empty[Long, Set[String]],
          uidToExmap = Map.empty[Long, TlaEx]
      )

    phi match {
      /** Recursive case, connectives */
      case OperEx(oper, args @ _*) if oper == TlaBoolOper.and || oper == TlaBoolOper.or =>
        /** First, process children */
        val processedChildArgs: Seq[StaticAnalysisData] =
          args.map(staticAnalysis(_, vars, initialFrozenVarSet, initialLetInOperBodyMap, manuallyAssigned))

        /** Compute parent delta from children */
        def deltaConnective(args: Seq[BoolFormula]) =
          if (oper == TlaBoolOper.and) Or(args: _*) else And(args: _*)

        val delta: deltaType =
          (vars map { v =>
            val childVals = processedChildArgs.map { rd =>
              /** Take the current delta_v. We know none of them are None by construction */
              rd.delta(v)
            }
            (v, deltaConnective(childVals))
          }).toMap

        /**
         * The seen/colloc/noColloc sets are merely unions of their respective child sets.
         * In the case of the frozen mapping, the domains are disjoint so ++ suffices
         */
        val childRecData: StaticAnalysisData = processedChildArgs.foldLeft(defaultArgs) { (a, b) =>
          StaticAnalysisData(
              a.seen ++ b.seen,
              a.collocSet ++ b.collocSet,
              a.nonCollocSet ++ b.nonCollocSet,
              delta,
              a.frozen ++ b.frozen, // Key sets disjoint by construction
              a.uidToExmap ++ b.uidToExmap
          )
        }

        /** S is the set of all possible seen pairs */
        val S: collocSetType = for { x <- childRecData.seen; y <- childRecData.seen } yield (x, y)

        /**
         * At an AND node, all pairs not yet processed, that are not known to
         * be non-collocated, are collocated. At an OR branch, the opposite is true.
         */
        oper match {
          case TlaBoolOper.and =>
            childRecData.copy(collocSet = S -- childRecData.nonCollocSet)
          case TlaBoolOper.or =>
            childRecData.copy(nonCollocSet = S -- childRecData.collocSet)
        }

      /** Base case, assignment candidates */
      case OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx(name)), star) =>
        // if `name` has any manual assignments, this assignment candidate is ignored
        if (!manuallyAssigned.contains(name)) {
          val n: Long = phi.ID.id

          /** delta_v creates a fresh variable from the unique ID if name == v */
          val delta: deltaType = (vars map { v =>
            (v, if (name == v) Variable(n) else False())
          }).toMap

          StaticAnalysisData(
              seen = Set[Long](n),
              /** Mark the node as seen */
              collocSet = Set[(Long, Long)]((n, n)),
              /** A terminal node, is always collocated exactly with itself */
              nonCollocSet = Set.empty[(Long, Long)],
              delta = delta,
              frozen = Map(n -> (initialFrozenVarSet ++ findPrimes(star))),
              /** At a terminal node, we know the exact values for the frozen sets */
              uidToExmap = Map(n -> phi)
              /** Add the mapping from n to its expr. */
          )
        } else {
          defaultArgs
        }

      /** Base case, manual assignments */
      case OperEx(BmcOper.assign, OperEx(TlaActionOper.prime, NameEx(name)), star) =>
        val n: Long = phi.ID.id

        /** delta_v creates a fresh variable from the unique ID if name == v */
        val delta: deltaType = (vars map { v =>
          (v, if (name == v) Variable(n) else False())
        }).toMap

        StaticAnalysisData(
            seen = Set[Long](n),
            /** Mark the node as seen */
            collocSet = Set[(Long, Long)]((n, n)),
            /** A terminal node, is always collocated exactly with itself */
            nonCollocSet = Set.empty[(Long, Long)],
            delta = delta,
            frozen = Map(n -> (initialFrozenVarSet ++ findPrimes(star))),
            /** At a terminal node, we know the exact values for the frozen sets */
            uidToExmap = Map(n -> phi)
            /** Add the mapping from n to its expr. */
        )

      /** Recursive case, quantifier */
      case OperEx(TlaBoolOper.exists, NameEx(_), star, subPhi) =>
        /** All primes in the star expr. contribute to the frozen sets of subPhi */
        val newFrozenVarSet = initialFrozenVarSet ++ findPrimes(star)

        /** Recurse on the child with a bigger frozen set */
        staticAnalysis(subPhi, vars, newFrozenVarSet, initialLetInOperBodyMap, manuallyAssigned)

      case OperEx(TlaControlOper.ifThenElse, star, thenExpr, elseExpr) =>
        /** All primes in the star expr. contribute to the frozen sets of bothe subexpr. */
        val starPrimes = findPrimes(star)
        val newFrozenVarSet = initialFrozenVarSet ++ starPrimes

        /** Recurse on both branches */
        val thenResults = staticAnalysis(thenExpr, vars, newFrozenVarSet, initialLetInOperBodyMap, manuallyAssigned)
        val elseResults = staticAnalysis(elseExpr, vars, newFrozenVarSet, initialLetInOperBodyMap, manuallyAssigned)

        /** Continue as with disjunction */
        val delta: deltaType = (vars map { v =>
          (v, And(thenResults.delta(v), elseResults.delta(v)))
        }).toMap

        val seen = thenResults.seen ++ elseResults.seen
        val childCollocSet = thenResults.collocSet ++ elseResults.collocSet
        val jointFrozen = thenResults.frozen ++ elseResults.frozen

        val S: collocSetType = for { x <- seen; y <- seen } yield (x, y)

        val jointMap = thenResults.uidToExmap ++ elseResults.uidToExmap

        StaticAnalysisData(seen, childCollocSet, S -- childCollocSet, delta, jointFrozen, jointMap)

      /** Recursive case, nullary LetIn */
      case LetInEx(body, defs @ _*) =>
        // Sanity check, all operators must be nullary
        assert(defs.forall { _.formalParams.isEmpty })

        /** First, analyze the bodies, to reuse later */
        val bodyResults = (defs map { d =>
          d.name -> staticAnalysis(d.body, vars, initialFrozenVarSet, initialLetInOperBodyMap, manuallyAssigned)
        }).toMap

        /** Then, analyze the body, with the bodyResults map */
        staticAnalysis(body, vars, initialFrozenVarSet, initialLetInOperBodyMap ++ bodyResults, manuallyAssigned)

      /** Nullary apply */
      case OperEx(TlaOper.apply, NameEx(operName)) =>
        // Apply may appear in higher order operators, so it might not be possible to pre-analyze
        initialLetInOperBodyMap.getOrElse(operName, defaultArgs)

      /** In the other cases, return the default args */
      case _ => defaultArgs
    }
  }

  /**
   * Point of access mathod.
   * @param vars Set of all variables relevant for phi.
   * @param phi Input formula
   * @param complete Optional parameter. If set to true, the produced specification
   *                   is valid as a standalone specification. Otherwise it is
   *                   designed to be passed to the
   *                   [[at.forsyte.apalache.tla.assignments.SMTInterface SMT interface]].
   * @return SMT specification string, encoding the assignment problem for `phi`.
   */
  def apply(
      vars: Set[String], phi: TlaEx, complete: Boolean = false
  ): String = {

    import AlphaTLApTools._

    val manuallyAssigned = ManualAssignments.findAll(phi)

    /** Extract the list of leaf ids, the collocated set, the delta mapping and the frozen mapping */
    val StaticAnalysisData(seen, colloc, _, delta, frozen, uidMap) =
      staticAnalysis(phi, vars, Set[String](), Map.empty[String, StaticAnalysisData], manuallyAssigned).simplified

    /**
     * We need two subsets of colloc, Colloc_\triangleleft for \tau_A
     * and Colloc_Vars for \tau_C
     */

    /**
     * Membership check for Colloc_Vars,
     * a pair (i,j) belongs to Colloc_Vars, if both i and j label assignment candidates
     * for the same variable.
     */
    def minimalCoveringClash(i: Long, j: Long): Boolean = {
      val ex_i = uidMap.get(i)
      val ex_j = uidMap.get(j)

      vars.exists(v =>
        ex_i.exists(isVarCand(v, _)) &&
          ex_j.exists(isVarCand(v, _))
      )
    }

    /**
     * Membership check for Colloc_\tl,
     * a pair (i,j) belongs to Colloc_\tl, if there is a variable v,
     * such that i labels an assignment candidate for v and
     * v is in the frozen set of j.
     *
     * Checking that j is a candidate is unnecessary, by construction,
     * since seen/colloc only contain assignment candidate IDs.
     */
    def triangleleft(i: Long, j: Long): Boolean = {
      val ex_i = uidMap.get(i)

      vars.exists(v =>
        ex_i.exists(isVarCand(v, _)) &&
          frozen(j).contains(v)
      )
    }

    /** Use the filterings to generate the desired sets */
    val colloc_Vars = colloc filter { case (i, j) => minimalCoveringClash(i, j) }
    val colloc_tl = colloc filter { case (i, j) => triangleleft(i, j) }

    val toSmt: BoolFormula => String = toSmt2(_)

    /** \theta_C^*^ */
    val thetaCStar = delta.values.map(toSmt)

    /** \theta^\E!^ */
    val thetaE = colloc_Vars withFilter { case (i, j) => i < j } map { case (i, j) =>
      toSmt(Neg(And(Variable(i), Variable(j))))
    }

    /** \theta_A^*^ */
    val thetaAStar = colloc_tl map { case (i, j) =>
      toSmt(Implies(And(Variable(i), Variable(j)), LtFns(i, j)))
    }

    /** \theta^inj^ */
    val thetaInj = for { i <- seen; j <- seen if i < j } yield toSmt(NeFns(i, j))

    /** The constant/funciton declaration commands */
    val typedecls = seen.map("( declare-fun %s_%s () Bool )".format(m_varSym, _)).mkString("\n")
    val fndecls = "\n( declare-fun %s ( Int ) Int )\n".format(m_fnSym)

    /** Assert all of the constraints, as defined in \theta */
    val constraints =
      (thetaCStar ++ thetaE ++ thetaAStar ++ thetaInj).map(str => "( assert %s )".format(str)).mkString("\n")

    /** Partial return, sufficient for the z3 API */
    val ret = typedecls + fndecls + constraints

    /** Possibly produce standalone spec */
    if (complete) {
      val logic = "( set-logic QF_UFLIA )\n"
      val end = "\n( check-sat )\n( get-model )\n( exit )"

      return logic + ret + end

    }

    ret
  }

}
