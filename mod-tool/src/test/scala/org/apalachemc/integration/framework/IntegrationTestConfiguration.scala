package org.apalachemc.integration.framework

import at.forsyte.apalache.io.config.{SMTEncoding, SMTSolver}

/** Identifies one environment in which an integration-test suite can run. */
sealed trait IntegrationTestConfiguration {
  def id: String
  def environment: Map[String, String]

  /** Verifies that a worker process exposes the environment represented by this configuration. */
  private[integration] def validateEnvironment(environment: Map[String, String]): Unit
}

object IntegrationTestConfiguration {
  private[integration] val ActiveConfigurationProperty = "apalache.cli.test.configuration"

  /** Runs command suites that do not depend on an SMT solver or encoding. */
  case object GENERAL extends IntegrationTestConfiguration {
    override val id: String = "general"
    override val environment: Map[String, String] = Map.empty

    override private[integration] def validateEnvironment(environment: Map[String, String]): Unit = ()
  }

  /** Runs checker command suites with a concrete solver and encoding. */
  final case class CheckerConfiguration private (
      id: String,
      solver: SMTSolver,
      encoding: SMTEncoding)
      extends IntegrationTestConfiguration {
    override val environment: Map[String, String] = Map(
        "SMT_SOLVER" -> solver.name,
        "SMT_ENCODING" -> encoding.name,
    )

    override private[integration] def validateEnvironment(environment: Map[String, String]): Unit = {
      this.environment.foreach { case (name, expected) =>
        require(
            environment.get(name).contains(expected),
            s"Integration-test worker $id expected $name=$expected, but got ${environment.get(name).getOrElse("<unset>")}",
        )
      }
    }
  }

  val OOPSLA19_Z3: CheckerConfiguration =
    CheckerConfiguration("oopsla19-z3", SMTSolver.Z3, SMTEncoding.OOPSLA19)
  val OOPSLA19_CVC5: CheckerConfiguration =
    CheckerConfiguration("oopsla19-cvc5", SMTSolver.CVC5, SMTEncoding.OOPSLA19)
  val ARRAYS_Z3: CheckerConfiguration =
    CheckerConfiguration("arrays-z3", SMTSolver.Z3, SMTEncoding.Arrays)

  val checkerConfigurations: Set[CheckerConfiguration] = Set(OOPSLA19_Z3, OOPSLA19_CVC5, ARRAYS_Z3)
  val values: Vector[IntegrationTestConfiguration] = Vector(GENERAL, OOPSLA19_Z3, OOPSLA19_CVC5, ARRAYS_Z3)

  private val byId = values.map(configuration => configuration.id -> configuration).toMap

  private[integration] def parse(id: String): IntegrationTestConfiguration =
    byId.getOrElse(
        id,
        throw new IllegalArgumentException(
            s"Unknown integration-test configuration '$id'; expected one of ${values.map(_.id).mkString(", ")}"),
    )

  private[integration] def active: IntegrationTestConfiguration =
    parse(Option(System.getProperty(ActiveConfigurationProperty)).getOrElse(GENERAL.id))

  private[integration] def validateSupported(configurations: Set[IntegrationTestConfiguration]): Unit =
    require(configurations.nonEmpty, "An integration-test suite must support at least one configuration")
}
