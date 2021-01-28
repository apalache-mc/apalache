package at.forsyte.apalache.tla.assignments.passes

import java.io.File
import java.nio.file.Path

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.io.PrettyWriter
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.{
  TlaExTransformation,
  TransformationTracker
}
import at.forsyte.apalache.tla.lir.transformations.standard._
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
  * PrimingPass adds primes to the variables in state initializers and constant initializers.
  */
class PrimingPassImpl @Inject()(
    options: PassOptions,
    tracker: TransformationTracker,
    @Named("AfterPriming") nextPass: Pass with TlaModuleMixin
) extends PrimingPass
    with LazyLogging {

  /**
    * The name of the pass
    *
    * @return the name associated with the pass
    */
  override def name: String = "PrimingPass"

  private def trSeq(seq: Seq[TlaExTransformation]): TlaExTransformation = {
    ex =>
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

    // The solution to breaking the impossible dependency of Inlining > Priming > Cover Analysis > Inlining
    // is for Priming to manually inline just the relevant Init/CInit operator
    val baseTransformationSequence =
      List(
        InlinerOfUserOper(bodyMap, tracker),
        LetInExpander(tracker, keepNullary = true),
        // the second pass of Inliner may be needed, when the higher-order operators were inlined by LetInExpander
        InlinerOfUserOper(bodyMap, tracker)
      )

    val cinitPrimed =
      options.get[String]("checker", "cinit") match {
        case Some(name) =>
          val operatorBody = bodyMap(name).body
          val primeTransformer = Prime(constSet, tracker) // add primes to constants
          val cinitPrimedName = name + "Primed"
          logger.info(s"  > Introducing $cinitPrimedName for $name'")
          val newBody = trSeq(baseTransformationSequence :+ primeTransformer)(
            deepCopy(operatorBody)
          )
          Some(TlaOperDecl(cinitPrimedName, List(), newBody))

        case _ =>
          None
      }

    val initName =
      options.getOrElse("checker", "init", "Init").asInstanceOf[String]
    val primeTransformer = Prime(varSet, tracker)
    val initPrimedName = initName + "Primed"
    logger.info(s"  > Introducing $initPrimedName for $initName'")
    // add primes to variables
    val newBody = trSeq(baseTransformationSequence :+ primeTransformer)(
      deepCopy(bodyMap(initName).body)
    )
    val initPrimed = Some(TlaOperDecl(initPrimedName, List(), newBody))

    val newDeclarations: Seq[TlaDecl] = declarations ++ Seq(
      cinitPrimed,
      initPrimed
    ).flatten
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
