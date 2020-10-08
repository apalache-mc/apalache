package at.forsyte.apalache.tla.types.passes

import java.io.{File, FileWriter, PrintWriter}
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.smt.SmtTools.And
import at.forsyte.apalache.tla.lir.storage.{BodyMapFactory, ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.types._
import at.forsyte.apalache.tla.types.smt.Z3TypeSolver.{Solution, SolutionFunction, UnsatCore}
import at.forsyte.apalache.tla.types.smt.{SmtVarGenerator, Z3TypeSolver}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

class TypeAnnotationPassImpl @Inject()(
                                        val options : PassOptions,
                                        sourceStore: SourceStore,
                                        changeListener: ChangeListener,
                                        @Named( "AfterTypes" ) nextPass : Pass with TlaModuleMixin
                                      )
  extends TypeAnnotationPass with LazyLogging {

  // For now, read from options later
  private val useSoftConstraints : Boolean = false
  private val primeConsistency   : Boolean = true

  private val smtVarGen  = new SmtVarGenerator
  private val typeVarGen = new TypeVarGenerator

  def countCases( solutionFn: SolutionFunction ): Map[String,Int] = {
    val initMap = Map(
      "ibs" -> 0,
      "tup" -> 0,
      "rec" -> 0,
      "fn" -> 0,
      "set" -> 0,
      "seq" -> 0,
      "op" -> 0
    )
    val varTypes = smtVarGen.allVars.withFilter( _.isInstanceOf[SmtTypeVariable] ) map { t =>
      solutionFn( t.asInstanceOf[SmtDatatype] )
    }
    varTypes.foldLeft( initMap ) { ( m, v ) =>
      v match {
        case IntT | BoolT | StrT => m + ( "ibs" -> ( m( "ibs" ) + 1 ) )
        case _ : TupT => m + ( "tup" -> ( m( "tup" ) + 1 ) )
        case _ : RecT => m + ( "rec" -> ( m( "rec" ) + 1 ) )
        case _ : FunT => m + ( "fn" -> ( m( "fn" ) + 1 ) )
        case _ : SetT => m + ( "set" -> ( m( "set" ) + 1 ) )
        case _ : SeqT => m + ( "seq" -> ( m( "seq" ) + 1 ) )
        case _ : OperT => m + ( "op" -> ( m( "op" ) + 1 ) )
        case _ => m
      }
    }
  }


  /**
    * The pass name.
    *
    * @return the name associated with the pass
    */
  override def name : String = "TypeAnnotationPass"

  /**
    * Run the pass.
    *
    * @return true, if the pass was successful
    */
  override def execute( ) : Boolean = {

    val startTime = System.currentTimeMillis()
    val module = tlaModule.get

    logger.info( "Started type pass")

    val limits = SpecLimits.getLimits( module.declarations )

    val operDecls = module.operDeclarations
    val nonOperDecls = module.constDeclarations ++ module.varDeclarations

    val bodyMap = BodyMapFactory.makeFromDecls( operDecls )

    val globalNameContext = new GlobalBindingBuilder( smtVarGen ).build(
      nonOperDecls, primeConsistency
    )

    val templateGenerator =
      new UserDefinedTemplateGenerator( limits, smtVarGen, globalNameContext, bodyMap )

    // We compute the dependency graph, so we can get constraints
    // for all operators, by just generating templates for roots
    val dependencies = DependencyGraph.construct( bodyMap )
    val roots = dependencies.root.children

    val virtualCalls = operDecls withFilter { d => roots.contains( d.name) } map {
      case decl@TlaOperDecl( name, fParams, _ ) =>
        val e = smtVarGen.getFresh
        val ts = smtVarGen.getNFresh( fParams.length )
        val template = templateGenerator.makeTemplate( decl )
        val constraint = template( e +: ts )
        name -> (e, ts, constraint)
    }

    val constraints = And( virtualCalls.map {
      case (_, (_, _, c)) => c
    } : _* )

    val solver = new Z3TypeSolver( useSoftConstraints = useSoftConstraints, typeVarGen, limits )

    val observedFields = Option( templateGenerator.getObservedFields )
    logger.info( "Start SMT")
    val ret = solver.solve( smtVarGen.allVars, constraints, observedFields )
    logger.info("End SMT")

    val runtime = (System.currentTimeMillis() - startTime) / 1000.0

    ret match {
      case Solution( solution ) =>
        val operatorContext = templateGenerator.getCtx

        // Root-level operators won't have call sites if they're basic roots,
        // but we know their types (they're determined by the templates)
        val partialSolution = ( virtualCalls map {
          case (name, (e, ts, _)) =>
            name -> OperT( TupT( ts map solution : _* ), solution( e ) )
        } ).toMap

        // TODO: propagate the solution to other passes

        val interpretedSolution = new SolutionInterpreter( typeVarGen ).interpret(
          partialSolution,
          bodyMap,
          operatorContext,
          globalNameContext,
          solution
        )

        // dump the result to a file
        val outStr = interpretedSolution.toList.sortBy( _._1 ) map {
          case (k, v) => s"$k: $v"
        } mkString "\n"

        val countStr = (countCases( solution ) map {
          case (k,v) => s"$k:$v"
        }).mkString(";")


        val outdir = options.getOrError( "io", "outdir" ).asInstanceOf[Path]
        val pw = new PrintWriter( new FileWriter( new File( outdir.toFile, "out-types.txt" ), false ) )
        pw.write( runtime.toString )
        pw.write( "\n\n" )
        pw.write( countStr )
        pw.write( "\n\n" )
        pw.write( outStr )
        pw.close()
        logger.info( "Ended type pass")
        true
      case UnsatCore( core ) =>
        // We already get the core as conflicting expressions, not labels
        val outStr = core map { _.toString } mkString "\n"

        // Next, we want to show which variable corresponds to which expression

        // First we construct the UID -> TlaEx mapping
        val backMap = bodyMap.foldLeft( Map.empty[UID, TlaEx] ) {
          case (partialMap, (_, TlaOperDecl( _, _, body ))) => partialMap ++ aux.uidToExMap( body )
        }

        val ctx = templateGenerator.getCtx

        val locator = SourceLocator(sourceStore.makeSourceMap, changeListener )

        // Then, we pretty-print the information from the OperatorContext
        val varDescription = ctx.toList.sortBy { _._1.length } flatMap {
          case (stack, varAsgn) =>
            val prefix = stack map backMap mkString "->"
            varAsgn.toList.sortBy { _._1.id } flatMap {
              case (uid, tv) =>
                backMap.get( uid ) map { ex =>
                  s"$prefix->$tv: $ex, ${locator.sourceOf(ex)}"
                }
            }
        }

        val descrStr = varDescription mkString "\n"

        // Lastly, we dump to a file
        val outdir = options.getOrError( "io", "outdir" ).asInstanceOf[Path]
        val pw = new PrintWriter( new FileWriter( new File( outdir.toFile, "out-usc.txt" ), false ) )
        pw.write( runtime.toString )
        pw.write( "\n\n" )
        pw.write( outStr )
        pw.write( "\n\n" )
        pw.write( descrStr )
        pw.close()
        logger.info( "Ended type pass")
        false
    }
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  //  override def next( ) : Option[Pass] = tlaModule map { m =>
  //    nextPass.setModule( m )
  //    nextPass
  //  }

  // Temporary, for experiments
  override def next( ) : Option[Pass] = None

}
