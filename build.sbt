Global / onChangedBuildSource := ReloadOnSourceChanges
ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.4.0"

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
      "org.scalatest" %% "scalatest" % "3.2.17" % "test",
      "com.lihaoyi" %% "pprint" % "0.8.1",
      "com.lihaoyi" %% "fastparse" % "3.0.2"
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
