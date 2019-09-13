package at.forsyte.apalache.tla.assignments.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.assignments._
import at.forsyte.apalache.tla.imp.findBodyOf
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.storage.{BodyMapFactory, ChangeListener, SourceLocator}
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
                                    @Named("AfterAssignment") nextPass: Pass with TlaModuleMixin )
      extends AssignmentPass with LazyLogging {
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

    val initTransitionsRaw = ste( initReplacedDecls, initName )
    /** Finally, we sort them for convenience */
    val trSort = new TransitionOrder( SourceLocator( sourceStore.makeSourceMap, changeListener ) )
    val initTransitionsSorted = trSort.sourceSort( initTransitionsRaw )
    // drop selections because of lacking implementation further on
    val initTransitions = initTransitionsSorted.map( _._2 ).toList

    for ((t, i) <- initTransitions.zipWithIndex) {
      logger.debug("Initial transition #%d:\n   %s".format(i, t))
    }

    val nextName = options.getOption("checker", "next", "Next").asInstanceOf[String]

    val nextTransitionsRaw = ste(initReplacedDecls,nextName)
    val nextTransitionsSorted = trSort.sourceSort( nextTransitionsRaw )
    // drop selections because of lacking implementation further on
    val nextTransitions = nextTransitionsSorted.map( _._2 ).toList

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

    // We do not add intReplacedDecls

    import ModuleManipulator.defaultNames._

    // We insert all the special values as operators
    val initDecls = ModuleManipulator.declsFromTransitions( initDefaultName, initTransitionsRaw )
    val nextDecls = ModuleManipulator.declsFromTransitions( nextDefaultName, nextTransitionsRaw )
    val cinitDeclOpt = ModuleManipulator.optionalOperDecl( cinitDefaultName, cinitPrime )
    val notInvDeclOpt = ModuleManipulator.optionalOperDecl( notInvDefaultName, notInvariant )
    val notInvPDeclOpt = ModuleManipulator.optionalOperDecl( notInvPrimeDefaultName, notInvariantPrime )

    // Option[x] ++ Seq[x] = Iterable[x]
    // None ++ l = l
    // Some(a) ++ l = a +: l
    val newDecls = cinitDeclOpt ++ notInvDeclOpt ++ notInvPDeclOpt ++ initDecls ++ nextDecls

    val module = tlaModule.get
    val newModule = new TlaModule( module.name, module.imports, newDecls.toSeq ++ module.declarations )

    setModule(newModule)
    true
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] = {
    tlaModule map { m =>
      nextPass.setModule(m)
      nextPass
    }
  }
}
