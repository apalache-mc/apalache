ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "systems.informal"

libraryDependencies ++= Seq(
    "org.scala-sbt" % "sbt" % "1.6.2"
)

lazy val sbt_changeling = (project in file("."))
  .enablePlugins(SbtPlugin)
  .settings(
      name := "sbt-changeling"
  )
