ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.1.2"

lazy val root = (project in file("."))
  .settings(
    name := "archon",
    scalacOptions ++= Seq(
      "-Yexplicit-nulls",
      "-Ykind-projector",
      "-language:postfixOps"
    ),

    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.11" % "test",
    ),
    Test / envVars := Map(
      "TEST_RESOURCES_ROOT" -> file("src/test/resources").getAbsolutePath,
    ),
    Test / testOptions += Tests.Argument("-oF"),
    Test / fork := true,
  )
