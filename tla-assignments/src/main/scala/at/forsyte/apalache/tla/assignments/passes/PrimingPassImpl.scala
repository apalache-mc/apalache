package at.forsyte.apalache.tla.assignments.passes

import java.io.File
import java.nio.file.Path
import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
 * PrimingPass adds primes to the variables in state initializers and constant initializers.
 */
class PrimingPassImpl @Inject() (options: PassOptions, tracker: TransformationTracker, writerFactory: TlaWriterFactory,
    @Named("AfterPriming") nextPass: Pass with TlaModuleMixin)
    extends PrimingPass with LazyLogging {

  /**
   * The name of the pass
   *
   * @return the name associated with the pass
   */
  override def name: String = "PrimingPass"

  private def trSeq(seq: Seq[TlaExTransformation]): TlaExTransformation = { ex =>
    seq.foldLeft(ex) { case (partial, tr) => tr(partial) }
  }

  /**
   * Run the pass
   *
   * @return true, if the pass was successful
   */
  override def execute(): Boolean = {
    val declarations = tlaModule.get.declarations
    val varSet = tlaModule.get.varDeclarations.map(_.name).toSet
    val constSet = tlaModule.get.constDeclarations.map(_.name).toSet
    val deepCopy = DeepCopy(tracker)

    val bodyMap = BodyMapFactory.makeFromDecls(declarations)

    val cinitPrimed =
      options.get[String]("checker", "cinit") match {
        case Some(name) =>
          val operatorBody = bodyMap(name).body
          val primeTransformer = Prime(constSet, tracker) // add primes to constants
          val cinitPrimedName = name + "Primed"
          logger.info(s"  > Introducing $cinitPrimedName for $name'")
          val newBody = primeTransformer(deepCopy.deepCopyEx(operatorBody))
          // Safe constructor: cannot be recursive
          Some(TlaOperDecl(cinitPrimedName, List(), newBody))

        case _ =>
          None
      }

    val initName = options.getOrElse[String]("checker", "init", "Init")
    val primeTransformer = Prime(varSet, tracker)
    val initPrimedName = initName + "Primed"
    logger.info(s"  > Introducing $initPrimedName for $initName'")
    // add primes to variables
    val newBody = primeTransformer(
        deepCopy.deepCopyEx(bodyMap(initName).body)
    )
    // Safe constructor: cannot be recursive
    val initPrimed = Some(TlaOperDecl(initPrimedName, List(), newBody))

    val newDeclarations: Seq[TlaDecl] = declarations ++ Seq(cinitPrimed, initPrimed).flatten
    val newModule = new TlaModule(tlaModule.get.name, newDeclarations)

    writerFactory.writeModuleAllFormats(newModule.copy(name = "06_OutPriming"), TlaWriter.STANDARD_MODULES)

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
