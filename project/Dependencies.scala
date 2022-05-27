import sbt._

// NOTE: Dependencies that require specification of the Scala version use the
// `%%` operator to append the specified scala version.  See
// https://www.scala-sbt.org/1.x/docs/Library-Dependencies.html#Getting+the+right+Scala+version+with

// Follows SBT recommended structure
// See https://www.scala-sbt.org/1.x/docs/Organizing-Build.html#Tracking+dependencies+in+one+place
object Dependencies {

  object Deps {
    // Versions
    lazy val logbackVersion = "1.2.11"
    lazy val clistVersion = "3.5.1"

    // Libraries
    val clistCore = "org.backuity.clist" %% "clist-core" % clistVersion
    val clistMacros = "org.backuity.clist" %% "clist-macros" % clistVersion
    val commonsBeanutils =
      "commons-beanutils" % "commons-beanutils" % "1.9.4" // Apparently an untracked dependency of commonsConfiguration2
    val commonsConfiguration2 = "org.apache.commons" % "commons-configuration2" % "2.7"
    val commonsIo = "commons-io" % "commons-io" % "2.11.0"
    val guice = "com.google.inject" % "guice" % "5.1.0"
    val kiama = "org.bitbucket.inkytonik.kiama" %% "kiama" % "2.5.0"
    val logbackClassic = "ch.qos.logback" % "logback-classic" % logbackVersion
    val logbackCore = "ch.qos.logback" % "logback-core" % logbackVersion
    val logging = "com.typesafe.scala-logging" %% "scala-logging" % "3.9.5"
    val pureConfig = "com.github.pureconfig" %% "pureconfig" % "0.17.1"
    val scalaParserCombinators = "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1"
    val scalaCollectionContrib = "org.scala-lang.modules" %% "scala-collection-contrib" % "0.2.2"
    val scalaz = "org.scalaz" %% "scalaz-core" % "7.3.5"
    val slf4j = "org.slf4j" % "slf4j-api" % "1.7.36"
    val tla2tools = "org.lamport" % "tla2tools" % "1.7.0-SNAPSHOT"
    val ujson = "com.lihaoyi" %% "ujson" % "2.0.0"
    val z3 = "tools.aqua" % "z3-turnkey" % "4.8.17"
    val zioGrpcCodgen = "com.thesamet.scalapb.zio-grpc" %% "zio-grpc-codegen" % "0.5.0"
    val grpcNetty = "io.grpc" % "grpc-netty" % "1.41.0"
    val scalapbRuntimGrpc = "com.thesamet.scalapb" %% "scalapb-runtime-grpc" % scalapb.compiler.Version.scalapbVersion
  }

  // Test only depenendencies
  object TestDeps {
    // Libraries
    val junit = "junit" % "junit" % "4.13.2" % Test
    val scalacheck = "org.scalacheck" %% "scalacheck" % "1.16.0" % Test
    val easymock = "org.easymock" % "easymock" % "4.3" % Test

    val scalaTestVersion = "3.2.11"
    val scalatest = "org.scalatest" %% "scalatest" % scalaTestVersion % Test
    val scalatestplusEasymock = "org.scalatestplus" %% "easymock-4-3" % s"${scalaTestVersion}.0" % Test
    val scalatestplusJunit = "org.scalatestplus" %% "junit-4-13" % s"${scalaTestVersion}.0" % Test
    val scalatestplusScalacheck = "org.scalatestplus" %% "scalacheck-1-15" % s"${scalaTestVersion}.0" % Test

  }
}
