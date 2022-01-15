// Build-wide settings
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

// scalafmt configuration
ThisBuild / scalafmtFilter := "diff-dirty"

// Sub-projects
lazy val tla_assignments = (project in file("tla-assignments"))
lazy val tla_bmcmt = (project in file("tla-bmcmt"))
lazy val tla_io = (project in file("tla-io"))
lazy val tla_pp = (project in file("tla-pp"))
lazy val tla_types = (project in file("tla-types"))
lazy val tlair = (project in file("tlair"))

lazy val mod_distribution = (project in file("mod-distribution"))
lazy val mod_infra = (project in file("mod-infra"))
lazy val mod_tool = (project in file("mod-tool"))
  .dependsOn(tla_io)

// TODO A useful declaration is "test->test" which means test depends on test. This allows you to put utility code for testing in util/src/test/scala and then use that code in core/src/test/scala, for example.
