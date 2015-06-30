scalaVersion := "2.11.7"

//scalacOptions += "-Xlog-implicits"

name := "consbol"

version := "0.0.1"

organization := "uk.co.turingatemyhamster"

addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.0-M5" cross CrossVersion.full)

libraryDependencies += "com.github.mpilquist" %% "simulacrum" % "0.3.0"

libraryDependencies += "com.lihaoyi" %% "utest" % "0.3.1"

libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.1.3"

testFrameworks += new TestFramework("utest.runner.Framework")