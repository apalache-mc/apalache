import Dependencies._

///////////////////////////
// Project-wide settings //
///////////////////////////

// See https://www.scala-sbt.org/1.x/docs/Multi-Project.html#Build-wide+settings

ThisBuild / organization := "at.forsyte"
ThisBuild / version := "0.19.2-SNAPSHOT"
ThisBuild / scalaVersion := "2.12.15"

// https://oss.sonatype.org/content/repositories/snapshots/
ThisBuild / resolvers += Resolver.sonatypeRepo("snapshots")

// Shared dependencies accross all sub projects
ThisBuild / libraryDependencies ++= Seq(
    Deps.guice,
    Deps.logbackClassic,
    Deps.logbackCore,
    Deps.slf4j,
    Deps.tla2tools,
    Deps.z3,
    Deps.logging,
    Deps.scalaParserCombinators,
    // NOTE: I'm suggesting promoting this to system wide dep
    Deps.scalaz,
    TestDeps.junit,
    TestDeps.easymock,
    TestDeps.spotless,
    TestDeps.scalatest,
    TestDeps.scalacheck,
)

/////////////////////
// scalafmt config //
/////////////////////

import net.moznion.sbt.spotless.config._

// TODO configure to ratchet from unstable
ThisBuild / spotlessScala := ScalaConfig(
    scalafmt = ScalafmtConfig(
        version = "2.4.6",
    ),
)

////////////////////////////////////////////
// Dependencies used in multiple projects //
////////////////////////////////////////////

/////////////////////////////
// Sub-project definitions //
/////////////////////////////

lazy val tlaModuleTestSettings = Seq(
    // we have to tell SANY the location of Apalache modules for the tests
    Test / fork := true, // Forking is required for the system options to take effect in the tests
    Test / javaOptions += s"""-DTLA-Library=${(ThisBuild / baseDirectory).value / "src" / "tla"}""",
)

lazy val tlair = (project in file("tlair"))
  .settings(
      libraryDependencies ++= Seq(
          Deps.ujson,
          Deps.kiama,
      ),
  )

lazy val infra = (project in file("mod-infra"))
  .dependsOn(tlair)

// TODO: Why is this project prefixed with "tla"?
lazy val tla_io = (project in file("tla-io"))
  .dependsOn(tlair, infra)
  .settings(
      tlaModuleTestSettings,
      libraryDependencies ++= Seq(
          Deps.commonsIo,
          Deps.pureConfig,
      ),
  )

lazy val tla_types = (project in file("tla-types"))
  .dependsOn(tlair, infra, tla_io)
  .settings(
      tlaModuleTestSettings,
      libraryDependencies += Deps.commonsIo,
  )

lazy val tla_pp = (project in file("tla-pp"))
  .dependsOn(
      tlair,
      // property based tests depend on IR generators defined in the tlair tests
      // See https://www.scala-sbt.org/1.x/docs/Multi-Project.html#Per-configuration+classpath+dependencies
      tlair % "test->test",
      infra,
      tla_io,
      tla_types,
  )
  .settings(
      tlaModuleTestSettings,
      libraryDependencies += Deps.commonsIo,
  )

// Sub-projects
lazy val tla_assignments = (project in file("tla-assignments"))
  .dependsOn(tlair, infra, tla_io, tla_pp, tla_types)
  .settings(
      libraryDependencies += Deps.commonsIo,
  )

lazy val tla_bmcmt = (project in file("tla-bmcmt"))
  .dependsOn(tlair, infra, tla_io, tla_pp, tla_assignments)

lazy val tool = {
  (project in file("mod-tool"))
    .dependsOn(tlair, tla_io, tla_assignments, tla_bmcmt)
    .settings(
        libraryDependencies ++= Seq(
            Deps.commonsConfiguration2,
            Deps.commonsBeanutils,
            Deps.clistCore,
            Deps.clistMacros,
        ),
    )
}

lazy val distribution = (project in file("mod-distribution"))
  .dependsOn(tlair, tla_io, tla_assignments, tla_bmcmt, tool)


///////////////
// Packaging //
///////////////

// TODO Include the needed TLA resources etc. from src/assembly/bin.xml
// Define the main entrypoint and uber jar package
lazy val root = (project in file("."))
  .dependsOn(distribution)
  .settings(
    assembly / mainClass := Some("at.forsyte.apalache.tla.Tool"),
  )
