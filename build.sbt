name := "trepplein"
description := "Independent type-checker for the dependently typed theorem prover Lean"
homepage := Some(url("https://github.com/gebner/trepplein"))
startYear := Some(2017)
licenses := Seq("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.html"))

version := "1.0"

scalaVersion := "2.12.4"
crossScalaVersions := Seq("2.11.7")

libraryDependencies += "org.parboiled" %% "parboiled" % "2.1.4"
libraryDependencies += "com.github.scopt" %% "scopt" % "3.7.0"
libraryDependencies += "org.specs2" %% "specs2-core" % "4.0.2" % "test"

enablePlugins(JavaAppPackaging)
javaOptions in Universal ++= Seq("-J-Xss30m")

import scalariform.formatter.preferences._
import com.typesafe.sbt.SbtScalariform.ScalariformKeys
ScalariformKeys.preferences := ScalariformKeys.preferences.value
  .setPreference(DoubleIndentConstructorArguments, true)
