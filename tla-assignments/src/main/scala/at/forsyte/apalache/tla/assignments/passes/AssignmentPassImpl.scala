package at.forsyte.apalache.tla.assignments.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions}
import at.forsyte.apalache.tla.assignments.{AssignmentException, Converter, SpecWithTransitions, assignmentSolver}
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * This pass finds symbolic transitions in a TLA+ specification.
  */
class AssignmentPassImpl @Inject()(options: PassOptions,
                                   @Named("AfterAssignment") nextPass: Pass with SpecWithTransitionsMixin)
      extends AssignmentPass with LazyLogging {

  var tlaModule: Option[TlaModule] = None
  private var specWithTransitions: Option[SpecWithTransitions] = None

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
  override def execute(): Boolean = {
    val vars = tlaModule.get.declarations
      .filter(_.isInstanceOf[TlaVarDecl])
      .map(d => NameEx(d.name))
    val varSet = Set(vars.map(_.name): _*)

    // replace every variable x with x', so we can use the assignment solver
    def primeVars(e: TlaEx): TlaEx = e match {
      case NameEx(name) if varSet.contains(name) => tla.prime(e)
      case OperEx(op, args@_*) => OperEx(op, args.map(primeVars): _*)
      case _ => e
    }

    val initName = options.getOption("checker", "init", "Init").asInstanceOf[String]

    // since Converter and assignmentSolver do a lot of magic internally, substitute Init with primed variables first
    def replaceInit(decl: TlaDecl): TlaDecl = decl match {
      case TlaOperDecl(name, params, body) if name == initName =>
        if (params.nonEmpty) {
          throw new AssignmentException("Initializing operator %s has %d arguments, expected 0"
            .format(initName, params.length))
        } else {
          TlaOperDecl(name, params, primeVars(body))
        }

      case e@_ => e
    }

    val declarations = tlaModule.get.declarations.map(replaceInit)

    // let converter do its magic
    val converter = new Converter()
    converter.extract(declarations: _*)
    val initBody = findBodyOf(initName, declarations: _*)
    val sanitizedInit = converter.sanitize(initBody)

    val initAssignments = assignmentSolver.getSymbolicTransitions(varSet, sanitizedInit)
    val initTransitions =
      if (initAssignments.isEmpty) {
        throw new AssignmentException("Failed to extract variable assignments from " + initName)
      } else {
        // TODO: label the assignment expressions as assignments in a special database
        // for the moment just rely on that the assignment solver transforms the formulas in such a way
        // that all assignments come first
        initAssignments.get.map(_._2).toList
      }

    for ((t, i) <- initTransitions.zipWithIndex) {
      logger.debug("Initial transition #%d:\n   %s".format(i, t))
    }

    val nextName = options.getOption("checker", "next", "Next").asInstanceOf[String]
    val nextBody = findBodyOf(nextName, tlaModule.get.declarations: _*)
    val sanitizedNext = converter.sanitize(nextBody)
    val nextAssignments = assignmentSolver.getSymbolicTransitions(varSet, sanitizedNext)
    val nextTransitions =
      if (nextAssignments.isEmpty) {
        throw new AssignmentException("Failed to extract variable assignments from " + nextName)
      } else {
        // TODO: label the assignment expressions as assignments in a special database
        // for the moment just rely on that the assignment solver transforms the formulas in such a way
        // that all assignments come first
        nextAssignments.get.map(_._2).toList
      }

    for ((t, i) <- nextTransitions.zipWithIndex) {
      logger.debug("Next transition #%d:\n   %s".format(i, t))
    }

    val invName = options.getOption("checker", "inv", None).asInstanceOf[Option[String]]
    val invariant =
      if (invName.isDefined) {
        val invBody = findBodyOf(invName.get, tlaModule.get.declarations: _*)
        Some(converter.sanitize(tla.not(invBody)))
      } else {
        None
      }

    logger.info("Found %d initializing transitions and %d next transitions"
      .format(initTransitions.length, nextTransitions.length))

    specWithTransitions
      = Some(new SpecWithTransitions(tlaModule.get, initTransitions, nextTransitions, invariant))
    true
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] = {
    if (specWithTransitions.isDefined) {
      nextPass.setSpecWithTransitions(specWithTransitions.get)
      Some(nextPass)
    } else {
      None
    }
  }
}
