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
    TestDeps.scalatest,
    TestDeps.scalacheck,
)

/////////////////////
// scalafmt config //
/////////////////////

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

// Define the main entrypoint and uber jar package
lazy val root = (project in file("."))
  .dependsOn(distribution)
  .aggregate(
      // will propagate commands to these sub-projects
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
      name := "apalache",
      // Package definition
      Compile / packageBin / mappings ++= Seq(
          // Include theese assets in the compiled package at the specified locations
          ((ThisBuild / baseDirectory).value / "README.md" -> "README.md"),
          ((ThisBuild / baseDirectory).value / "LICENSE" -> "LICENSE"),
      ),
      assembly / assemblyJarName := s"apalache-pkg-${version.value}-full.jar",
      assembly / mainClass := Some("at.forsyte.apalache.tla.Tool"),
      assembly / assembledMappings += {
        val src_dir = (ThisBuild / baseDirectory).value / "src" / "tla"
        // See https://github.com/sbt/sbt-assembly/issues/227#issuecomment-283504401
        sbtassembly.MappingSet(
            None,
            Vector(
                (src_dir / "Apalache.tla") -> "tla2sany/StandardModules/Apalacha.tla",
                (src_dir / "Variants.tla") -> "tla2sany/StandardModules/Variants.tla",
            ),
        )
      },
  )

// Specify and build the docker file
enablePlugins(DockerPlugin)

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

  val fatJar = assembly.value
  val jarTarget = s"${dwd}/target/scala-2.12/${fatJar.name}"

  val runners = rootDir / "bin"
  val runnersTarget = s"${dwd}/bin"

  val modules = rootDir / "src" / "tla"
  val modulesTarget = s"${dwd}/src/tla"

  val license = rootDir / "LICENSE"
  val readme = rootDir / "README.md"

  new Dockerfile {
    from("eclipse-temurin:16")

    workDir(dwd)

    add(fatJar, jarTarget)
    add(runners, runnersTarget)
    add(license, s"${dwd}/${license.name}")
    add(readme, s"${dwd}/${readme.name}")
    add(modules, modulesTarget)

    // TLA parser requires all specification files to be in the same directory
    // We assume the user bind-mounted the spec dir into /var/apalache
    // In case the directory was not bind-mounted, we create one
    run("mkdir", "/var/apalache")

    // We need sudo to run apalache using the user (created in the entrypoint script)
    run("apt", "update")
    run("apt", "install", "sudo")

    entryPoint("/opt/apalache/bin/run-in-docker-container")
  }
}
