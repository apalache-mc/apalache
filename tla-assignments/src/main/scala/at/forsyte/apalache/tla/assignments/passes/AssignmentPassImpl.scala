package at.forsyte.apalache.tla.assignments.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions}
import at.forsyte.apalache.tla.assignments._
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.process.Renaming
import at.forsyte.apalache.tla.lir.storage.{BodyMapFactory, ChangeListener}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.transformations.standard._
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

// TODO:
// USE SymbolicTransitionPass

/**
  * This pass finds symbolic transitions in a TLA+ specification.
  */
class AssignmentPassImpl @Inject()( options: PassOptions,
                                    sourceStore: SourceStore,
                                    changeListener: ChangeListener,
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

  private def findOrThrow(
                           name: String,
                           msgPrefix: String,
                           decls: Seq[TlaDecl]
                         ) : Option[TlaEx] = {
    val nameOpt = options.getOption("checker", name, None).asInstanceOf[Option[String]]
    nameOpt map { n =>
      findBodyOf(n, decls: _*) match {
        case NullEx =>
          val msg = s"$msgPrefix $n not found"
          logger.error(msg)
          throw new IllegalArgumentException(msg)
        case body =>
          body
      }
    }
  }

  /**
    * Run the pass
    *
    * @return true, if the pass was successful
    */
  override def execute(): Boolean = {
    val tracker = TrackerWithListeners( changeListener )

    val decls = tlaModule.get.declarations

    val varSet = decls
      .filter(_.isInstanceOf[TlaVarDecl])
      .map(_.name).toSet
    val constSet = decls
      .filter(_.isInstanceOf[TlaConstDecl])
      .map(_.name).toSet

    val initName = options.getOption("checker", "init", "Init").asInstanceOf[String]

    val bodyMap = BodyMapFactory.makeFromDecls( decls )

    val primeTr = Prime( varSet, tracker )
    // We need an extra EqualityAsContainment, because priming
    // may change equality into asgn. candidates
    val eacTr = EqualityAsContainment( tracker )

    // since Converter and assignmentSolver do a lot of magic internally, substitute Init with primed variables first
    def replaceInit(decl: TlaDecl): TlaDecl = decl match {
      case TlaOperDecl(name, params, body) if name == initName =>
        if (params.nonEmpty) {
          throw new AssignmentException("Initializing operator %s has %d arguments, expected 0"
            .format(initName, params.length))
        } else {
          TlaOperDecl( name, params, eacTr( primeTr( body ) ) )
        }

      case e@_ => e
    }

    val initReplacedDecls = decls.map(replaceInit)

    val ste = new SymbolicTransitionExtractor( tracker )

    // drop selections because of lacking implementation further on
    val initTransitions = ste( initReplacedDecls, initName ).map( _._2 ).toList

    for ((t, i) <- initTransitions.zipWithIndex) {
      logger.debug("Initial transition #%d:\n   %s".format(i, t))
    }

    val nextName = options.getOption("checker", "next", "Next").asInstanceOf[String]

    // drop selections because of lacking implementation further on
    val nextTransitions = ste(initReplacedDecls,nextName).map( _._2 ).toList

    for ((t, i) <- nextTransitions.zipWithIndex) {
      logger.debug("Next transition #%d:\n   %s".format(i, t))
    }

    val cinit = findOrThrow( "cinit", "Constant initializer", decls )
    val cinitPrime = cinit map {
      body =>
        val ret = eacTr( Prime( constSet, tracker )( body ) )
        logger.debug(s"Constant initializer with primes\n    $ret")
        ret
    }

    val inv = findOrThrow( "inv", "Invariant", decls )
    val notInvariant = inv map { i =>
      val ret = tracker.track {
        x => tla.not(x)
      }(i)
      logger.debug(s"Negated invariant:\n   $ret")
      ret
    }

    val notInvariantPrime = notInvariant map { i =>
      val ret = eacTr( primeTr ( i ) )
      logger.debug(s"Negated invariant with primes\n   $ret")
      ret
    }

    logger.info("Found %d initializing transitions and %d next transitions"
      .format(initTransitions.length, nextTransitions.length))

    val newModule = new TlaModule(tlaModule.get.name, tlaModule.get.imports, decls)
    specWithTransitions
      = Some(new SpecWithTransitions(newModule, initTransitions, nextTransitions, cinitPrime, notInvariant, notInvariantPrime))
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
