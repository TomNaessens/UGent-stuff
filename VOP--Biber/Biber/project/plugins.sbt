// Comment to get more information during initialization
logLevel := Level.Warn

// The Typesafe repository
resolvers += "Typesafe repository" at "http://repo.typesafe.com/typesafe/releases/"

// Use the Play sbt plugin for Play projects
addSbtPlugin("play" % "sbt-plugin" % "2.1.0")

libraryDependencies ++= Seq(
  "org.jacoco" % "org.jacoco.core" % "0.5.10.201208310627" artifacts(Artifact("org.jacoco.core", "jar", "jar")),
  "org.jacoco" % "org.jacoco.report" % "0.5.10.201208310627" artifacts(Artifact("org.jacoco.report", "jar", "jar"))
)

addSbtPlugin("de.johoop" % "jacoco4sbt" % "1.2.4")
