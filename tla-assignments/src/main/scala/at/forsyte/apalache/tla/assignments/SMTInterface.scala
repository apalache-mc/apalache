package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import com.microsoft.z3._

/**
 * General interface for an SMT solver.
 *
 * Current implementation uses Z3.
 */
class SMTInterface {

  /**
   * Wraps a [[com.microsoft.z3.FuncInterp FuncInterp]].
   *
   * The [[apply]] method allows using a [[com.microsoft.z3.FuncInterp FuncInterp]]
   * as a function.
   *
   * @param m_fun    Wrapped function interpretation
   * @param m_varSym Symbol used for variables
   */
  private class FunWrapper[R <: Sort](m_fun: FuncInterp[R], m_varSym: String) {

    /** Return value for arguments outside the relevant subdomain. */
    protected val m_default: Int = m_fun.getElse.asInstanceOf[IntNum].getInt

    /**
     * Internal map, corresponds to the restriction of the function represented by `m_fun`
     * to the relevant subdomain.
     */
    protected val m_map: Map[String, Int] =
      (for { e: FuncInterp.Entry[R] <- m_fun.getEntries } yield (
          "%s_%s".format(m_varSym, e.getArgs.head),
          e.getValue.asInstanceOf[IntNum].getInt
      )).toMap

    /** The wrapper can be called like a function. */
    def apply(arg: String): Int = m_map.getOrElse(arg, m_default)

//    override def toString : String = m_map.toString
  }

  /**
   * Point of access method,
   *
   * @param p_spec   SMT specification string for the assignment problem,
   *                 as required by the underlying solver.
   * @param p_varSym Symbol used for variables.
   * @return Some(A), if there exists an assignment strategy A, satisfying the spec, otherwise None.
   */
  def apply(p_spec: String, p_varSym: String): Option[StrategyType] = {

    /** Initialize a context and solver */
    val ctx = new Context()
    val solver = ctx.mkSolver()

    /** Parse the spec and add it to the solver */
    solver.add(ctx.parseSMTLIB2String(p_spec, null, null, null, null): _*)

    /** If UNSAT, terminate */
    val status = solver.check.toString
    if (status != "SATISFIABLE")
      return None

    /** If SAT, get a model. */
    val m = solver.getModel

    /** Extract the rank function. Should be the only (non-const.) function */
    val fnDecl = m.getFuncDecls

    fnDecl.size match {
      case 0 =>
        /** Only happens if Next is exactly 1 assignment */
        val trues =
          m.getConstDecls.withFilter(x => m.getConstInterp(x).isTrue).map(_.getName.toString)
        Some(trues.map(x => UID(x.substring(2).toInt)))

      case 1 =>
        /** Wrap the function so it can be used to sort the sequence later. */
        val wrap = new FunWrapper(m.getFuncInterp(fnDecl(0)), p_varSym)

        assert(wrap("") == m.getFuncInterp(fnDecl(0)).getElse.asInstanceOf[IntNum].getInt)

        /** Extract all constants which are set to true */
        val trues = m.getConstDecls.withFilter(x => m.getConstInterp(x).isTrue).map(_.getName.toString)

        /** Sort by rank */
        val sorted = trues.sortBy(x => wrap.apply(x))

        /* return */
        Some(sorted.map(x => UID(x.substring(2).toInt)))

      /** Should not happen if spec comes from [[AssignmentStrategyEncoder]] */
      case _ => None
    }
  }

}
