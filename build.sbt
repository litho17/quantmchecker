name := "quantmchecker"

version := "1.0"

scalaVersion := "2.12.1"

libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.5"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5" % "test"

libraryDependencies += "com.regblanc" %% "scala-smtlib" % "0.2.2"

// https://mvnrepository.com/artifact/org.checkerframework/checker
libraryDependencies += "org.checkerframework" % "checker" % "2.5.3"

// libraryDependencies += "com.ibm.wala" % "com.ibm.wala.shrike" % "1.5.0"
// libraryDependencies +=  "com.ibm.wala" % "com.ibm.wala.util" % "1.5.0"
// libraryDependencies += "com.ibm.wala" % "com.ibm.wala.core" % "1.5.0"
// libraryDependencies += "com.ibm.wala" % "com.ibm.wala.cast" % "1.5.0"
// libraryDependencies += "com.ibm.wala" % "com.ibm.wala.cast.java" % "1.5.0"
