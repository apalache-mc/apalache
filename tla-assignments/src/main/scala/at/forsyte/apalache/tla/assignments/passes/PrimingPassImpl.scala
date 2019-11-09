package at.forsyte.apalache.tla.assignments.passes

import java.io.File
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.io.PrettyWriter
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard._
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * PrimingPass adds primes to the variables in state initializers and constant initializers.
  */
class PrimingPassImpl @Inject()(options: PassOptions,
                                tracker: TransformationTracker,
                                @Named("AfterPriming") nextPass: Pass with TlaModuleMixin )
      extends PrimingPass with LazyLogging {
  /**
    * The name of the pass
    *
    * @return the name associated with the pass
    */
  override def name: String = "PrimingPass"

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
          val operatorBody = bodyMap(name)._2
          val primeTransformer = Prime(constSet, tracker) // add primes to constants
          val cinitPrimedName = name + "Primed"
          logger.info(s"  > Introducing $cinitPrimedName as $name'")
          Some(TlaOperDecl(cinitPrimedName,
                           List(),
                           primeTransformer(deepCopy(operatorBody))))

        case _ =>
          None
      }

    val initName = options.getOrElse("checker", "init", "Init").asInstanceOf[String]
    val primeTransformer = Prime(varSet, tracker)
    val initPrimedName = initName + "Primed"
    logger.info(s"  > Introducing $initPrimedName as $initName'")
    // add primes to variables
    val initPrimed = Some(TlaOperDecl(initPrimedName, List(), primeTransformer(deepCopy(bodyMap(initName)._2))))

    val newDeclarations: Seq[TlaDecl] = declarations ++ Seq(cinitPrimed, initPrimed).flatten
    val newModule = new TlaModule(tlaModule.get.name, newDeclarations)

    val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
    PrettyWriter.write(newModule, new File(outdir.toFile, "out-priming.tla"))

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
