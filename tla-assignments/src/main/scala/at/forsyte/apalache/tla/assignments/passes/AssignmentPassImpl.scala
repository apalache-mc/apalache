package at.forsyte.apalache.tla.assignments.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions}
import at.forsyte.apalache.tla.assignments._
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.db.BodyDB
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

// TODO:
// USE SymbolicTransitionPass

/**
  * This pass finds symbolic transitions in a TLA+ specification.
  */
class AssignmentPassImpl @Inject()(options: PassOptions,
                                   environmentHandler: EnvironmentHandler,
                                   sourceStore: SourceStore,
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
    val allDeclarations = OperatorHandler.uniqueVarRename(tlaModule.get.declarations, sourceStore)

    val vars = allDeclarations
      .filter(_.isInstanceOf[TlaVarDecl])
      .map(d => NameEx(d.name))
    val varSet = vars.map(_.name).toSet

    // replace every variable x with x', so we can use the assignment solver
    def primeVars(e: TlaEx): TlaEx = e match {
      case ne @ NameEx(name) if varSet.contains(name) =>
        val newEx = environmentHandler.identify(tla.prime(e))
        sourceStore.onTransformation(ne, newEx)
        newEx

      case oe @ OperEx(op, args@_*) =>
        val newEx = environmentHandler.identify(OperEx(op, args.map(primeVars): _*))
        sourceStore.onTransformation(oe, newEx)
        newEx


      case _ => e
    }

    val initName = options.getOption("checker", "init", "Init").asInstanceOf[String]

    val transformer = new Transformer()

    val bodyDB = new BodyDB

    val decls = allDeclarations.map(
      {
        case TlaOperDecl( name, params, body ) =>
          TlaOperDecl( name, params, transformer.explicitLetIn( body )( sourceStore ) )
        case e@_ => e
      }
    )

    transformer.extract( decls  :_* )(bodyDB)

    // TODO: why do we call a pass inside a pass?
    val stp = new SymbolicTransitionPass( bodyDB, sourceStore )

    // since Converter and assignmentSolver do a lot of magic internally, substitute Init with primed variables first
    def replaceInit(decl: TlaDecl): TlaDecl = decl match {
      case TlaOperDecl(name, params, body) if name == initName =>
        if (params.nonEmpty) {
          throw new AssignmentException("Initializing operator %s has %d arguments, expected 0"
            .format(initName, params.length))
        } else {
          TlaOperDecl( name, params, primeVars( transformer.inlineAll( body )( bodyDB, sourceStore ) ) )
        }

      case e@_ => e
    }

    val declarations = allDeclarations.map(replaceInit)

    // drop selections because of lacking implementation further on
    val initTransitions = stp( declarations, initName ).map( _._2 ).toList

    for ((t, i) <- initTransitions.zipWithIndex) {
      logger.debug("Initial transition #%d:\n   %s".format(i, t))
    }

    val nextName = options.getOption("checker", "next", "Next").asInstanceOf[String]

    // drop selections because of lacking implementation further on
    val nextTransitions = stp(declarations,nextName).map( _._2 ).toList

    for ((t, i) <- nextTransitions.zipWithIndex) {
      logger.debug("Next transition #%d:\n   %s".format(i, t))
    }

    val invName = options.getOption("checker", "inv", None).asInstanceOf[Option[String]]
    val invariant =
      if (invName.isDefined) {
        val invBody = findBodyOf(invName.get, allDeclarations: _*)
        if (invBody == NullEx) {
          val msg = "Invariant definition %s not found".format(invName.get)
          logger.error(msg)
          throw new IllegalArgumentException(msg)
        }
        val notInv = transformer.sanitize(tla.not(invBody))( bodyDB, sourceStore )
        logger.debug("Negated invariant:\n   %s".format(notInv))
        Some(notInv)
      } else {
        None
      }

    logger.info("Found %d initializing transitions and %d next transitions"
      .format(initTransitions.length, nextTransitions.length))

    val newModule = new TlaModule(tlaModule.get.name, tlaModule.get.imports, allDeclarations)
    specWithTransitions
      = Some(new SpecWithTransitions(newModule, initTransitions, nextTransitions, invariant))
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
