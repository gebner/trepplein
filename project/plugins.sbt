resolvers += Classpaths.sbtPluginReleases
logLevel := Level.Warn

addSbtPlugin("org.scalariform" % "sbt-scalariform" % "1.8.0")

addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.2.2")
