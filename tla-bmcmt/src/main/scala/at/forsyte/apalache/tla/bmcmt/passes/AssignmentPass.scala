package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.tla.assignments.{Converter, assignmentSolver}
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.db.DB

class AssignmentPass(idDatabase: DB[UID, TlaEx]) extends Pass[TlaModule, CheckerInput] {
  private var tlaModule: Option[TlaModule] = None
  private var checkerInput: Option[CheckerInput] = None
  // TODO: define by options
  val initName = "Init"
  val nextName = "Next"
  val invName = "Inv"


  /**
    * The name of the pass
    *
    * @return the name associated with the pass
    */
  override def name: String = "AssignmentFinder"

  /**
    * Run the pass
    *
    * @return true, if the pass was successful
    */
  override def run(): Boolean = {
    // TODO: once Jure fixes the interface, we will just use a dependency here
    Converter.clear()

    val vars = getInput.get.declarations.filter(_.isInstanceOf[TlaVarDecl]).map(d => NameEx(d.name))
    val varSet = Set(vars.map(_.name): _*)

    // replace every variable x with x', so we can use the assignment solver
    def primeVars(e: TlaEx): TlaEx = e match {
      case NameEx(name) if varSet.contains(name) => tla.prime(e)
      case OperEx(op, args@_*) => OperEx(op, args.map(primeVars): _*)
      case _ => e
    }

    // since Converter and assignmentSolver do a lot of magic internally, substitute Init with primed variables first
    def replaceInit(decl: TlaDecl): TlaDecl = decl match {
      case TlaOperDecl(name, params, body) if name == initName =>
        if (params.nonEmpty) {
          throw new CheckerException("Initializing operator %s has %d arguments, expected 0"
            .format(initName, params.length))
        } else {
          TlaOperDecl(name, params, primeVars(body))
        }

      case e@_ => e
    }

    val declarations = tlaModule.get.declarations.map(replaceInit)

    Converter.extract(declarations: _*)
    val initBody = findBodyOf(initName, declarations: _*)
    val sanitizedInit = Converter.sanitize(initBody)

    val initAssignments = assignmentSolver.getSymbolicTransitions(varSet, sanitizedInit)
    val initTransitions =
      if (initAssignments.isEmpty) {
        throw new CheckerException("Failed to extract variable assignments from " + initName)
      } else {
        // TODO: label the assignment expressions as assignments in a special database
        // for the moment just rely on that the assignment solver transforms the formulas in such a way
        // that all assignments come first
        initAssignments.get.map(_._2)
      }

    val nextBody = findBodyOf(nextName, tlaModule.get.declarations: _*)
    val sanitizedNext = Converter.sanitize(nextBody)
    val nextAssignments = assignmentSolver.getSymbolicTransitions(varSet, sanitizedNext)
    val nextTransitions =
      if (nextAssignments.isEmpty) {
        throw new CheckerException("Failed to extract variable assignments from " + nextName)
      } else {
        // TODO: label the assignment expressions as assignments in a special database
        // for the moment just rely on that the assignment solver transforms the formulas in such a way
        // that all assignments come first
        nextAssignments.get.map(_._2)
      }

    val invariant = findBodyOf(invName, tlaModule.get.declarations: _*)

    checkerInput = Some(new CheckerInput(initTransitions.toList, nextTransitions.toList, Some(invariant)))
    true
  }

  /**
    * Get the input to the pass.
    *
    * @return the input, possibly None
    */
  override def getInput: Option[TlaModule] = {
    tlaModule
  }

  /**
    * Set the input to the pass.
    *
    * @param in the input
    */
  override def setInput(in: TlaModule): Unit = {
    tlaModule = Some(in)
  }

  /**
    * Get the output of the pass.
    *
    * @return the output
    */
  override def getOutput: Option[CheckerInput] = {
    checkerInput
  }
}
