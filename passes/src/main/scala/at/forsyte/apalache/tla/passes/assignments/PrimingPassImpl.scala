package at.forsyte.apalache.tla.passes.assignments

import at.forsyte.apalache.infra.passes.DerivedPredicates
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.decorateWithPrime
import at.forsyte.apalache.tla.lir.transformations.standard._
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * PrimingPass adds primes to the variables in state initializers and constant initializers.
 */
class PrimingPassImpl @Inject() (
    derivedPreds: DerivedPredicates,
    tracker: TransformationTracker,
    writerFactory: TlaWriterFactory)
    extends PrimingPass with LazyLogging {

  override def name: String = "PrimingPass"

  override def execute(tlaModule: TlaModule): PassResult = {
    val declarations = tlaModule.declarations
    val varSet = tlaModule.varDeclarations.map(_.name).toSet
    val constSet = tlaModule.constDeclarations.map(_.name).toSet
    val deepCopy = DeepCopy(tracker)

    val bodyMap = BodyMapFactory.makeFromDecls(declarations)

    val cinitPrimed = derivedPreds.cinit.map { name =>
      val operatorBody = bodyMap(name).body
      val primeTransformer = decorateWithPrime(constSet, tracker) // add primes to constants
      val cinitPrimedName = name + "Primed"
      logger.info(s"  > Introducing $cinitPrimedName for $name'")
      val newBody = primeTransformer(deepCopy.deepCopyEx(operatorBody))
      // Safe constructor: cannot be recursive
      TlaOperDecl(cinitPrimedName, List(), newBody)
    }

    val initName = derivedPreds.init
    val primeTransformer = decorateWithPrime(varSet, tracker)
    val initPrimedName = initName + "Primed"
    logger.info(s"  > Introducing $initPrimedName for $initName'")
    // add primes to variables
    val newBody = primeTransformer(
        deepCopy.deepCopyEx(bodyMap(initName).body)
    )

    // Safe constructor: cannot be recursive
    val initPrimed = Some(TlaOperDecl(initPrimedName, List(), newBody))

    val newDeclarations: Seq[TlaDecl] = declarations ++ Seq(cinitPrimed, initPrimed).flatten
    val newModule = tlaModule.copy(declarations = newDeclarations)

    writeOut(writerFactory, newModule)

    Right(newModule)
  }

  override def dependencies = Set(ModuleProperty.Configured)

  override def transformations = Set(ModuleProperty.Primed)
}
