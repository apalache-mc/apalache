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
ThisBuild / libraryDependencies ++= {

  // NOTE: Dependencies that require specification of the Scala version use the
  // `%%` operator to append the specified scala version.  See
  // https://www.scala-sbt.org/1.x/docs/Library-Dependencies.html#Getting+the+right+Scala+version+with

  val libraryDeps = {
    val logbackVersion = "1.2.10"
    Seq(
        "com.google.inject" % "guice" % "5.0.1",
        "ch.qos.logback" % "logback-classic" % logbackVersion,
        "ch.qos.logback" % "logback-core" % logbackVersion,
        "org.slf4j" % "slf4j-api" % "1.7.33",
        "org.lamport" % "tla2tools" % "1.7.0-SNAPSHOT",
        "io.github.tudo-aqua" % "z3-turnkey" % "4.8.14",
        // Scala-compiler specific
        "com.typesafe.scala-logging" %% "scala-logging" % "3.9.4",
        "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.0",
        // NOTE: I'm suggesting promoting this to system wide dep
        "org.scalaz" %% "scalaz-core" % "7.3.5",
    )
  }

  val testDeps = {
    val spotlessVersion = "2.20.0"
    Seq(
        "junit" % "junit" % "4.13.2",
        "org.easymock" % "easymock" % "4.3",
        "com.diffplug.spotless" % "spotless-maven-plugin" % spotlessVersion,
        // Scala-compiler specific
        "org.scalatest" %% "scalatest" % "3.0.1",
        "org.scalacheck" %% "scalacheck" % "1.15.4",
    ).map(_ % Test)
  }

  libraryDeps ++ testDeps
}

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

lazy val commonsIo = "commons-io" % "commons-io" % "2.11.0"

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
          "com.lihaoyi" %% "ujson" % "1.4.4",
          "org.bitbucket.inkytonik.kiama" %% "kiama" % "2.5.0",
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
          commonsIo,
          "com.github.pureconfig" %% "pureconfig" % "0.17.1",
      ),
  )

lazy val tla_types = (project in file("tla-types"))
  .dependsOn(tlair, infra, tla_io)
  .settings(
      tlaModuleTestSettings,
      libraryDependencies += commonsIo,
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
      libraryDependencies += commonsIo,
  )

// Sub-projects
lazy val tla_assignments = (project in file("tla-assignments"))
  .dependsOn(tlair, infra, tla_io, tla_pp, tla_types)
  .settings(
      libraryDependencies += commonsIo,
  )

lazy val tla_bmcmt = (project in file("tla-bmcmt"))
  .dependsOn(tlair, infra, tla_io, tla_pp, tla_assignments)

lazy val tool = {
  (project in file("mod-tool"))
    .dependsOn(tlair, tla_io, tla_assignments, tla_bmcmt)
    .settings(
        libraryDependencies ++= {
          val clistVersion = "3.5.1"
          Seq(
              "org.apache.commons" % "commons-configuration2" % "2.7",
              "commons-beanutils" % "commons-beanutils" % "1.9.4",
              "org.backuity.clist" %% "clist-core" % clistVersion,
              "org.backuity.clist" %% "clist-macros" % clistVersion,
          )
        },
    )
}

lazy val distribution = (project in file("mod-distribution"))
  .dependsOn(tlair, tla_io, tla_assignments, tla_bmcmt, tool)
