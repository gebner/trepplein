name := "trepplein"

version := "1.0"

scalaVersion := "2.12.1"

libraryDependencies += "org.parboiled" %% "parboiled" % "2.1.4"
libraryDependencies += "com.github.scopt" %% "scopt" % "3.5.0"
libraryDependencies += "org.specs2" %% "specs2-core" % "3.8.8" % "test"

enablePlugins(JavaAppPackaging)
javaOptions in Universal ++= Seq("-J-Xss30m", "-J-Xmx300m")
