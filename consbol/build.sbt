lazy val sharedSettings = Seq(
//scalacOptions += "-Xlog-implicits",

  scalaVersion := "2.11.7",
  version := "0.0.1",
  organization := "uk.co.turingatemyhamster"
  )

lazy val util = crossProject.settings(
  name := "consbol-util",
  libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value % "provided",
  libraryDependencies += "org.scala-lang" % "scala-compiler" % scalaVersion.value % "provided",
  addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.0-M5" cross CrossVersion.full)
  ).settings(sharedSettings : _*)

lazy val utilJS = util.js
lazy val utilJVM = util.jvm

lazy val core = crossProject.settings(
  name := "consbol-core",
  addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.0-M5" cross CrossVersion.full),
  libraryDependencies += "com.github.mpilquist" %% "simulacrum" % "0.3.0",
  libraryDependencies += "com.lihaoyi" %%% "utest" % "0.3.1",
  //libraryDependencies += "com.lihaoyi" %%% "fastparse" % "0.1.7",
  testFrameworks += new TestFramework("utest.runner.Framework")
  ).settings(sharedSettings : _*).dependsOn(util)

lazy val coreJS = core.js.settings(
  libraryDependencies += "com.github.japgolly.fork.scalaz" %%% "scalaz-core" % "7.1.3"
  )

lazy val coreJVM = core.jvm.settings(
//  scalacOptions += "-Xlog-implicits",
  libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.1.3"
  )


lazy val server = crossProject.settings(
  name := "consbol-server",
  libraryDependencies += "com.lihaoyi" %%% "scalatags" % "0.5.2"
  ).settings(sharedSettings : _*).dependsOn(core)

lazy val serverJS = server.js.settings(
  libraryDependencies += "be.doeraene" %%% "scalajs-jquery" % "0.8.0"
)

lazy val serverJVM = server.jvm.enablePlugins(SbtWeb).settings(
  libraryDependencies += "com.typesafe.akka" %% "akka-http-experimental" % "1.0-RC4",
  libraryDependencies += "org.webjars" % "jquery" % "2.1.3",
  libraryDependencies += "org.webjars.npm" % "jqtree" % "1.1.0",
  (crossTarget in (serverJS, Compile, fastOptJS)) := crossTarget.value / "classes" / "public" / "javascript",
  (resources in Compile) += (fastOptJS in (serverJS, Compile)).value.data,
  includeFilter in (Assets, LessKeys.less) := "*.less",
  excludeFilter in (Assets, LessKeys.less) := "_*.less",
  WebKeys.packagePrefix in Assets := "public/",
  (managedClasspath in Runtime) += (packageBin in Assets).value
  ).settings(Revolver.settings : _*)


lazy val root = project.in(file(".")).
  aggregate(serverJS, serverJVM).
  settings(
    publish := {},
    publishLocal := {}
  )



