name := "trepplein"

version := "1.0"

scalaVersion := "2.12.2"
crossScalaVersions := Seq("2.11.7")

libraryDependencies += "org.parboiled" %% "parboiled" % "2.1.4"
libraryDependencies += "com.github.scopt" %% "scopt" % "3.6.0"
libraryDependencies += "org.specs2" %% "specs2-core" % "3.9.1" % "test"

enablePlugins(JavaAppPackaging)
javaOptions in Universal ++= Seq("-J-Xss30m", "-J-Xmx300m")
