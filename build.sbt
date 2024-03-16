Global / onChangedBuildSource := ReloadOnSourceChanges
ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.3.3"

lazy val root = (project in file("."))
  .settings(
    name := "archon",
    scalacOptions ++= Seq(
      "-Yexplicit-nulls",
      "-Ykind-projector",
      "-language:postfixOps",
      "-Xfatal-warnings",
      "-feature",
      "-deprecation",
      "-language:implicitConversions",
      "-new-syntax",
    ),
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.17" % "test",
      "com.lihaoyi" %% "pprint" % "0.8.1",
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
