import scala.sys.process._
import Dependencies._

///////////////////////////
// Project-wide settings //
///////////////////////////

name := "apalache"
maintainer := "apalache@informal.org"

// See https://www.scala-sbt.org/1.x/docs/Multi-Project.html#Build-wide+settings
ThisBuild / organizationName := "Informal Systems Inc."
ThisBuild / organizationHomepage := Some(url("https://informal.systems"))
ThisBuild / licenses += "Apache 2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0")

// We store the version in a bare file to make accessing and updating the version trivial
ThisBuild / versionFile := (ThisBuild / baseDirectory).value / "VERSION"
ThisBuild / version := scala.io.Source.fromFile(versionFile.value).mkString.trim

ThisBuild / organization := "at.forsyte"
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
    Deps.scalaz,
    TestDeps.junit,
    TestDeps.easymock,
    TestDeps.scalatest,
    TestDeps.scalacheck,
    TestDeps.scalatestplusEasymock,
    TestDeps.scalatestplusJunit,
    TestDeps.scalatestplusScalacheck,
)

////////////////////////////
// Linting and formatting //
////////////////////////////

// scalafmt
// TODO: Remove if we decide we are happy with allways reformatting all
// Only check/fix against (tracked) files that have changed relative to the trunk
// ThisBuild / scalafmtFilter := "diff-ref=origin/unstable"
ThisBuild / scalafmtPrintDiff := true

// scalafix
// https://scalacenter.github.io/scalafix/docs/rules/RemoveUnused.html
ThisBuild / scalacOptions ++= Seq("-Ywarn-unused")
ThisBuild / semanticdbVersion := scalafixSemanticdb.revision

///////////////////////////////
// Test configuration //
///////////////////////////////

// NOTE: Include these settings in any projects that require Apalache's TLA+ modules
lazy val tlaModuleTestSettings = Seq(
    // we have to tell SANY the location of Apalache modules for the tests
    Test / fork := true, // Forking is required for the system options to take effect in the tests
    Test / javaOptions += s"""-DTLA-Library=${(ThisBuild / baseDirectory).value / "src" / "tla"}""",
)

lazy val testSettings = Seq(
    // Configure the test reporters for concise but informative output.
    // See https://www.scalatest.org/user_guide/using_scalatest_with_sbt
    // for the meaning of the flags.
    Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-oCDEH")
)

/////////////////////////////
// Sub-project definitions //
/////////////////////////////

lazy val tlair = (project in file("tlair"))
  .settings(
      testSettings,
      libraryDependencies ++= Seq(
          Deps.ujson,
          Deps.kiama,
      ),
  )

lazy val infra = (project in file("mod-infra"))
  .dependsOn(tlair)
  .settings(
      testSettings
  )

lazy val tla_io = (project in file("tla-io"))
  .dependsOn(
      tlair,
      // property based tests depend on IR generators defined in the tlair tests
      // See https://www.scala-sbt.org/1.x/docs/Multi-Project.html#Per-configuration+classpath+dependencies
      tlair % "test->test",
      infra,
  )
  .settings(
      testSettings,
      tlaModuleTestSettings,
      libraryDependencies ++= Seq(
          Deps.commonsIo,
          Deps.pureConfig,
      ),
  )

lazy val tla_types = (project in file("tla-types"))
  .dependsOn(tlair, infra,
      // property based tests depend on IR generators defined in the tlair tests
      // See https://www.scala-sbt.org/1.x/docs/Multi-Project.html#Per-configuration+classpath+dependencies
      tlair % "test->test", tla_io)
  .settings(
      testSettings,
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
      testSettings,
      tlaModuleTestSettings,
      libraryDependencies += Deps.commonsIo,
  )

lazy val tla_assignments = (project in file("tla-assignments"))
  .dependsOn(tlair, infra, tla_io, tla_pp, tla_types)
  .settings(
      testSettings,
      libraryDependencies += Deps.commonsIo,
  )

lazy val tla_bmcmt = (project in file("tla-bmcmt"))
  .dependsOn(tlair, infra, tla_io, tla_pp, tla_assignments)
  .settings(
      testSettings
  )

lazy val tool = (project in file("mod-tool"))
  .dependsOn(tlair, tla_io, tla_assignments, tla_bmcmt)
  .enablePlugins(BuildInfoPlugin)
  .settings(
      testSettings,
      // The following buildInfo values will be available in the source
      // code in the `apalache.BuildInfo` singleton.
      // See https://github.com/sbt/sbt-buildinfo
      buildInfoPackage := "apalache",
      buildInfoKeys := {
        val build = scala.sys.process.Process("git describe --tags --always").!!.trim
        Seq[BuildInfoKey](
            BuildInfoKey.map(version) { case (k, v) =>
              if (isSnapshot.value) (k -> build) else (k -> v)
            },
            BuildInfoKey.action("build")(build),
        )
      },
      libraryDependencies ++= Seq(
          Deps.commonsConfiguration2,
          Deps.commonsBeanutils,
          Deps.clistCore,
          Deps.clistMacros,
      ),
  )

lazy val distribution = (project in file("mod-distribution"))
  .dependsOn(tlair, tla_io, tla_assignments, tla_bmcmt, tool)
  .settings(
      testSettings
  )

///////////////
// Packaging //
///////////////

lazy val apalacheCurrentPackage = taskKey[File]("Set the current executable apalche-mc to the latest package")

// Define the main entrypoint and uber jar package
lazy val root = (project in file("."))
  .enablePlugins(UniversalPlugin, sbtdocker.DockerPlugin)
  .dependsOn(distribution)
  .aggregate(
      // propagate commands to these sub-projects
      tlair,
      infra,
      tla_io,
      tla_types,
      tla_pp,
      tla_assignments,
      tla_bmcmt,
      tool,
      distribution,
  )
  .settings(
      testSettings,
      // Package definition
      Compile / packageBin / mappings ++= Seq(
          // Include theese assets in the compiled package at the specified locations
          ((ThisBuild / baseDirectory).value / "README.md" -> "README.md"),
          ((ThisBuild / baseDirectory).value / "LICENSE" -> "LICENSE"),
      ),
      // Assembly constructs our "fat jar"
      assembly / assemblyJarName := s"apalache-pkg-${version.value}-full.jar",
      assembly / mainClass := Some("at.forsyte.apalache.tla.Tool"),
      assembly / assembledMappings += {
        val src_dir = (ThisBuild / baseDirectory).value / "src" / "tla"
        // See https://github.com/sbt/sbt-assembly/issues/227#issuecomment-283504401
        sbtassembly.MappingSet(
            None,
            Vector(
                (src_dir / "Apalache.tla") -> "tla2sany/StandardModules/Apalache.tla",
                (src_dir / "Variants.tla") -> "tla2sany/StandardModules/Variants.tla",
                (src_dir / "__rewire_tlc_in_apalache.tla") -> "tla2sany/StandardModules/__rewire_tlc_in_apalache.tla",
            ),
        )
      },
      // Package the distribution files
      Universal / mappings ++= Seq(
          // The fat jar
          assembly.value -> "lib/apalache.jar",
          (ThisBuild / baseDirectory).value / "LICENSE" -> "LICENSE",
      ),
      apalacheCurrentPackage := {
        val log = streams.value.log
        val pkg = (Universal / packageZipTarball).value
        val (unzipped, _) = IO.split(pkg.toString)
        val target_dir = (Universal / target).value
        val current_pkg = (Universal / target).value / "current-pkg"
        log.info(s"Unpacking package ${pkg} to ${target_dir}")
        // send outputs directly to std{err,out} instead of logging here
        // to avoid misleading logging output from tar
        // See https://github.com/informalsystems/apalache/pull/1382
        (s"tar zxvf ${pkg} -C ${target_dir}" !)
        log.info(s"Symlinking ${current_pkg} -> ${unzipped}")
        s"ln -sfn ${unzipped} ${current_pkg}" ! log
        file(unzipped)
      },
  )

docker / imageNames := {
  val img: String => ImageName = s =>
    ImageName(
        namespace = Some("ghcr.io/informalsystems"),
        repository = name.value,
        tag = Some(s),
    )
  Seq(
      img(version.value),
      img("latest"),
  )
}

docker / dockerfile := {
  val rootDir = (ThisBuild / baseDirectory).value
  // Docker Working Dir
  val dwd = "/opt/apalache"

  val pkg = apalacheCurrentPackage.value

  val runner = rootDir / "bin" / "run-in-docker-container"
  val runnerTarget = s"${dwd}/bin/run-in-docker-container"
  val readme = rootDir / "README.md"

  new Dockerfile {
    from("eclipse-temurin:16")

    workDir(dwd)

    add(pkg, ".")
    add(runner, runnerTarget)
    add(readme, s"${dwd}/${readme.name}")

    // TLA parser requires all specification files to be in the same directory
    // We assume the user bind-mounted the spec dir into /var/apalache
    // but, in case the directory was not bind-mounted, we create one
    run("mkdir", "/var/apalache")

    // We need sudo to run apalache using the user (created in the entrypoint script)
    run("apt", "update")
    run("apt", "install", "sudo")

    entryPoint("/opt/apalache/bin/run-in-docker-container")
  }
}

//////////////
// appendix //
//////////////

// For some reason `scalafmtFilter` doesn't register as being used, tho it is
// so this quiets the erroneous linting.
Global / excludeLintKeys += scalafmtFilter

lazy val versionFile = settingKey[File]("Location of the file tracking the project version")

// These tasks are used in our bespoke release pipeline
// TODO(shon): Once we've changed our packaging to conform to more standard SBT structures and practices,
// we should consider moving to a release pipeline based around sbt-release.
// See https://github.com/informalsystems/apalache/issues/1248

lazy val printVersion = taskKey[Unit]("Print the current version")
printVersion := {
  println((ThisBuild / version).value)
}

lazy val removeVersionSnapshot = taskKey[Unit]("Remove version snapshot from the version file")
removeVersionSnapshot := {
  val releaseVersion = (ThisBuild / version).value.stripSuffix("-SNAPSHOT")
  IO.writeLines((ThisBuild / versionFile).value, Seq(releaseVersion))
}

lazy val setVersion = inputKey[Unit]("Set the version recorded in the version file")
setVersion := {
  val version: String = complete.Parsers.spaceDelimited("<args>").parsed(0)
  IO.writeLines((ThisBuild / versionFile).value, Seq(version))
}

lazy val incrVersion = taskKey[String]("Increment to the next patch snapshot version")
incrVersion := {
  val fullVersion = (ThisBuild / version).value
  val currentVersion =
    try {
      fullVersion.split("-")(0)
    } catch {
      case _: ArrayIndexOutOfBoundsException =>
        throw new RuntimeException(s"Invalid version: ${fullVersion}")
    }
  val nextVersion = currentVersion.split("\\.") match {
    case Array(maj, min, patch) => {
      val nextPatch = ((patch.toInt) + 1).toString
      s"${maj}.${min}.${nextPatch}-SNAPSHOT"
    }
    case arr =>
      throw new RuntimeException(s"Invalid version: ${fullVersion}")
  }
  IO.writeLines((ThisBuild / versionFile).value, Seq(nextVersion))
  nextVersion
}
