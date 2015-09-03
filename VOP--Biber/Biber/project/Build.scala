import sbt._
import Keys._
import play.Project._
import de.johoop.jacoco4sbt.JacocoPlugin._

object ApplicationBuild extends Build {

  val appName         = "Biber"
  val appVersion      = "1.0-SNAPSHOT"

  lazy val s = Defaults.defaultSettings ++ Seq(jacoco.settings:_*)

  val appDependencies = Seq(
    // Add your project dependencies here,
    javaCore,
    javaJdbc,
    javaEbean,
    "commons-net" % "commons-net" % "20030805.205232",
    "postgresql" % "postgresql" % "9.1-901.jdbc4",
    "org.mindrot" % "jbcrypt" % "0.3m",
    "dom4j" % "dom4j" % "1.6.1",
    "org.apache.commons" % "commons-email" % "1.2",
    "org.apache.poi" % "poi-ooxml-schemas" % "3.9",
    "javax.mail" % "mail" % "1.4.1",
    "javax.activation" % "activation" % "1.1",
    "com.typesafe" % "play-plugins-util_2.10" % "2.1.0",
    "org.apache.poi" % "poi-ooxml" % "3.7",
    "org.apache.xmlbeans" % "xmlbeans" % "2.5.0",
    "org.apache.poi" % "poi" % "3.9",
    "net.sf.opencsv" % "opencsv" % "2.3",
    "org.seleniumhq.selenium" % "selenium-java" % "2.32.0" % "test"
  )

  val main = play.Project(appName, appVersion, appDependencies, settings = s).settings(
    resolvers += "jbcrypt repo" at "http://mvnrepository.com/",
    parallelExecution in jacoco.Config := false,
    jacoco.excludes in jacoco.Config := Seq("views.*", "utils.Hash", "utils.BCrypt", "default", "controllers.ref.*")
  )

  javaOptions in (Test) += "-Xrunjdwp:transport=dt_socket,server=y,suspend=n,address=9999"

}
