package at.forsyte.apalache.tla.bmcmt

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
    * Introduce a new predicate.
    * @return the name of the new predicate
    */
  def createPred(): String

  /**
    * Assert that a given predicate holds.
    * @param predName a predicate name
    */
  def assertPred(predName: String): Unit

  /**
    * Assert than an expression holds.
    * @param expr an expression in SMTLIB2
    */
  def assertSmt2(expr: String): Unit

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

