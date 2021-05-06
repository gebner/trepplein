name := "trepplein"
description := "Independent type-checker for the dependently typed theorem prover Lean"
homepage := Some(url("https://github.com/gebner/trepplein"))
startYear := Some(2017)
licenses := Seq("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.html"))
maintainer := "gebner@gebner.org"

version := "1.0"

scalaVersion := "2.13.5"

libraryDependencies += "com.github.scopt" %% "scopt" % "4.0.0"
libraryDependencies += "org.specs2" %% "specs2-core" % "4.10.6" % "test"

scalacOptions ++= Seq("-opt:l:inline", "-opt-inline-from:**", "-opt-warnings", "-deprecation")

enablePlugins(JavaAppPackaging)
javaOptions in Universal ++= Seq("-J-Xss30m")

import scalariform.formatter.preferences._
import com.typesafe.sbt.SbtScalariform.ScalariformKeys
ScalariformKeys.preferences := ScalariformKeys.preferences.value
  .setPreference(DoubleIndentConstructorArguments, true)
