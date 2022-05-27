// https://scalameta.org/scalafmt/docs/installation.html#sbt
addSbtPlugin("org.scalameta" % "sbt-scalafmt" % "2.4.6")
// https://github.com/sbt/sbt-assembly
addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "1.2.0")
// https://github.com/marcuslonnberg/sbt-docker
addSbtPlugin("se.marcuslonnberg" % "sbt-docker" % "1.9.0")
// https://github.com/scoverage/sbt-scoverage
addSbtPlugin("org.scoverage" % "sbt-scoverage" % "1.9.3")
// https://github.com/sbt/sbt-buildinfo
addSbtPlugin("com.eed3si9n" % "sbt-buildinfo" % "0.11.0")
// https://github.com/sbt/sbt-native-packager
addSbtPlugin("com.github.sbt" % "sbt-native-packager" % "1.9.9")
// https://scalacenter.github.io/scalafix/docs/users/installation.html
addSbtPlugin("ch.epfl.scala" % "sbt-scalafix" % "0.10.0")
// https://scalapb.github.io/zio-grpc/docs/installation
addSbtPlugin("com.thesamet" % "sbt-protoc" % "1.0.2")
libraryDependencies += "com.thesamet.scalapb.zio-grpc" %% "zio-grpc-codegen" % "0.5.0"

// Add the locally defined plugins
lazy val root = (project in file("."))
  .dependsOn(changelingPlugin)
  .settings(
      name := "apalache-plugins"
  )

lazy val changelingPlugin =
  ProjectRef(file("sbt-changeling"), "sbt_changeling")
