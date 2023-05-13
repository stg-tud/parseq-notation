lazy val root = project
  .in(file("."))
  .settings(
    name := "par-seq-notation",
    version := "0.2.0",
    scalaVersion := "3.2.2",
    libraryDependencies ++= Seq(
      //"org.scalatest" %% "scalatest" % "3.2.12", // % "test"
      //"org.scalatest" %% "scalatest" % "latest.integration", // % "test"
      //"junit" % "junit" % "4.13.2",
    )
  )
