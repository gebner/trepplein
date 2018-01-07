resolvers += Classpaths.sbtPluginReleases
logLevel := Level.Warn

resolvers += Resolver.sbtPluginRepo("releases")
addSbtPlugin("org.scalariform" % "sbt-scalariform" % "1.8.2")
addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.3.2")
