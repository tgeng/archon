Global / onChangedBuildSource := ReloadOnSourceChanges
ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.4.2"

lazy val root = (project in file("."))
  .settings(
    name := "archon",
    scalacOptions ++= Seq(
      "-Yexplicit-nulls",
      "-Ykind-projector",
      "-Xfatal-warnings",
      "-feature",
      "-deprecation",
      "-language:implicitConversions",
      "-new-syntax",
      "-indent",
    ),
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.18" % "test",
      "com.lihaoyi" %% "pprint" % "0.9.0",
      "com.lihaoyi" %% "fastparse" % "3.1.0",
      "com.lihaoyi" %% "os-lib" % "0.10.2",
      "org.scala-lang.modules" %% "scala-collection-contrib" % "0.3.0"
    ),
    Compile / unmanagedJars += {
      baseDirectory.value / "unmanaged" / "scalaz3_3-4.8.14-macos-aarch64.jar"
    },
    Test / envVars := Map(
      "TEST_RESOURCES_ROOT" -> file("src/test/resources").getAbsolutePath,
    ),
    Test / testOptions += Tests.Argument("-oF"),
    Test / fork := true,
    maxErrors := 1,
  )
