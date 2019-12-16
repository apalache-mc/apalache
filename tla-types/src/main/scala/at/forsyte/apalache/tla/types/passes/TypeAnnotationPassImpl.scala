package at.forsyte.apalache.tla.types.passes

import java.io.{File, FileWriter, PrintWriter}
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.types._
import at.forsyte.apalache.tla.types.smt.Z3TypeSolver.{Solution, UnsatCore}
import at.forsyte.apalache.tla.types.smt.{SmtVarGenerator, Z3TypeSolver}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

class TypeAnnotationPassImpl @Inject()(
                                        val options : PassOptions,
                                        @Named( "TBD" ) nextPass : Pass with TlaModuleMixin
                                      )
  extends TypeAnnotationPass with LazyLogging {

  // For now, read from options later
  private val useSoftConstraints : Boolean = false
  private val primeConsistency   : Boolean = true

  private val smtVarGen  = new SmtVarGenerator
  private val typeVarGen = new TypeVarGenerator

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
    val module = tlaModule.get
    val initOperName = options.getOrElse( "checker", "init", "Init" )
    val nextOperName = options.getOrElse( "checker", "next", "Next" )
    val cinitOperNameOpt = options.get[String]( "checker", "cinit" )
    val invOperNameOpt = options.get[String]( "checker", "inv" )

    val operDecls = module.operDeclarations
    val nonOperDecls = module.constDeclarations ++ module.varDeclarations

    val rootOpers = Seq( initOperName, nextOperName ) ++ cinitOperNameOpt ++ invOperNameOpt

//     We imagine, for type-checking purposes, a virtual top-level operator, with the body
//     Init /\ Next (/\ Inv /\ CInit)
//     Then, we only need to run the template once, for the body of this fictional operator

    val virtualBody = Builder.and( rootOpers map { opName =>
      Builder.appOp( Builder.name( opName ) )
    } : _* )

    val rootName = "__root"
    val rootDecl = TlaOperDecl( rootName, List.empty, virtualBody )

    val bodyMap = BodyMapFactory.makeFromDecls( rootDecl +: operDecls )
//    val bodyMap = BodyMapFactory.makeFromDecls( operDecls )

    val globalNameContext = new NameContextBuilder( smtVarGen ).build(
      nonOperDecls, primeConsistency
    )

    val templateGenerator =
      new UserDefinedTemplateGenerator( smtVarGen, globalNameContext, bodyMap )

//    val virtualCalls = operDecls map {
//      case TlaOperDecl( name, fParams, body ) =>
//        val e = smtVarGen.getFresh
//        val ts = smtVarGen.getNFresh( fParams.length )
//        val template = templateGenerator.makeTemplate( fParams, body )
//        val constraint = template( e +: ts )
//        name -> (e, ts, constraint)
//    }

//    val constraints = And( virtualCalls.map {
//      case (_, (_, _, c)) => c
//    } : _* )

    val e = smtVarGen.getFresh
    val template = templateGenerator.makeTemplate( List.empty, virtualBody )
    val constraints = template( e +: Nil )

    val solver = new Z3TypeSolver( useSoftConstraints = useSoftConstraints, typeVarGen )

    val ret = solver.solve( smtVarGen.allVars, constraints )

    ret match {
      case Solution( solution ) =>
        val operatorContext = templateGenerator.getCtx

//        val extendedSolution = ( virtualCalls map {
//          case (name, (e, ts, _)) =>
//            name -> ( ts match {
//              case Nil => solution( e )
//              case _ => OperT( TupT( ts map solution : _* ), solution( e ) )
//            } )
//        } ).toMap

        val extendedSolution = bodyMap map {
          case (opName, (fParams, _)) =>
            opName -> ( fParams.length match {
              case 0 => typeVarGen.getUnique
              case n => OperT( TupT( typeVarGen.getNUnique( n ) : _* ), typeVarGen.getUnique )
            } )
        }

        // TODO: propagate the solution to other passes

        val interpretedSolution = new SolutionInterpreter( typeVarGen ).interpret(
          extendedSolution,
          bodyMap,
          operatorContext,
          globalNameContext,
          solution
        ) - rootName

        // dump the result to a file
        val outStr = interpretedSolution.toList.sortBy( _._1 ) map {
          case (k, v) => s"$k: $v"
        } mkString "\n"

        val outdir = options.getOrError( "io", "outdir" ).asInstanceOf[Path]
        val pw = new PrintWriter( new FileWriter( new File( outdir.toFile, "out-types.txt" ), false ) )
        pw.write( outStr )
        pw.close()
        true
      case UnsatCore( core ) =>
        // We already get the core as conflicting expressions, not labels
        val outStr = core map { _.toString } mkString "\n"

        // Next, we want to show which variable corresponds to which expression

        // First we construct the UID -> TlaEx mapping
        val backMap = bodyMap.foldLeft( Map.empty[UID, TlaEx] ) {
          case (partialMap, (_, (_, body))) => partialMap ++ aux.uidToExMap( body )
        }

        val ctx = templateGenerator.getCtx

        // Then, we pretty-print the information from the OperatorContext
        val varDescription = ctx.toList.sortBy { _._1.length } flatMap {
          case (stack, varAsgn) =>
            val prefix = stack map backMap mkString "->"
            varAsgn.toList.sortBy { _._1.id } flatMap {
              case (uid, tv) =>
                backMap.get( uid ) map { ex =>
                  s"$prefix->$tv: $ex"
                }
            }
        }

        val descrStr = varDescription mkString "\n"

        // Lastly, we dump to a file
        val outdir = options.getOrError( "io", "outdir" ).asInstanceOf[Path]
        val pw = new PrintWriter( new FileWriter( new File( outdir.toFile, "out-usc.txt" ), false ) )
        pw.write( outStr )
        pw.write( "\n\n" )
        pw.write( descrStr )
        pw.close()
        false
    }
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next( ) : Option[Pass] = tlaModule map { m =>
    nextPass.setModule( m )
    nextPass
  }
}
