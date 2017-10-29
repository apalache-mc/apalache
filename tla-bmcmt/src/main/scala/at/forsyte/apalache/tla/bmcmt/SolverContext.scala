package at.forsyte.apalache.tla.bmcmt

import com.microsoft.z3.{Context, Status}

/**
  * A context that stores the SMT constraints that are generated in the course of symbolic exploration.
  */
trait SolverContext {
  /**
    * The number of SMT pushes made so far.
    */
  def level: Int

  /**
    * Dispose whatever has to be disposed in the end.
    */
  def dispose()

  /**
    * Pop back the SMT context until a given level is reached
    * @param level a level to rollback to
    */
  def popTo(level: Int)

  /**
    * Assert that a given predicate holds
    * @param predName a predicate name
    */
  def assertPred(predName: String): Unit

  /**
    * Is the current context satisfiable?
    *
    * @return true if and only if the context is satisfiable
    */
  def isSat(): Boolean

  /**
    * Get the name of a constantly false predicate.
    * @return the name of a Boolean variable that is equivalent to False.
    */
  def predFalse(): String

  /**
    * Get the name of a constantly true predicate.
    * @return the name of a Boolean variable that is equivalent to True.
    */
  def predTrue(): String
}

/**
  * An implementation of a SolverContext with Z3.
  */
class Z3SolverContext extends SolverContext {
  var level: Int = 0
  val predFalse = "_pred0"
  val predTrue = "_pred1"
  private val z3context: Context = new Context()
  private val z3solver = z3context.mkSolver()

  /**
    * Dispose whatever has to be disposed in the end.
    */
  override def dispose(): Unit = {
    z3context.close()
  }

  /**
    * Assert that a given predicate holds
    *
    * @param predName a predicate name
    */
  override def assertPred(predName: String): Unit = {

  }

  override def popTo(newLevel: Int) = {
    level = newLevel
  }

  override def isSat(): Boolean = {
    z3solver.check() == Status.SATISFIABLE
  }
}