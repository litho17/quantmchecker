name := "quantmchecker"

version := "1.0"

scalaVersion := "2.12.1"

// libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.0"

libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.5"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5" % "test"

libraryDependencies += "com.regblanc" %% "scala-smtlib" % "0.2.2"

// https://mvnrepository.com/artifact/org.checkerframework/checker
libraryDependencies += "org.checkerframework" % "checker" % "2.5.3"