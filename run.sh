#!/bin/sh

export PATH=$HOME/Documents/workspace/checker-framework-2.4.0/checker/bin:$PATH

#javac -cp .:/Users/lumber/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar -AprintErrorStack -processor plv.colorado.edu.quantmchecker.QuantmChecker ~/Documents/workspace/quantmchecker/src/test/java/unit/MotivatingExample.java

scala_lib='/Users/lumber/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar'
class_files_location='target/scala-2.12/classes'
fully_qualified_name='plv.colorado.edu.quantmchecker.QuantmChecker'

# MAKE SURE THAT JAVAC WITHOUT -PROCESSOR WON'T ISSUE ERRORS

pwd=`pwd`
cd $class_files_location
javac -cp .:$scala_lib -AprintErrorStack -processor $fully_qualified_name $pwd/$1
#-AignoreRawTypeArguments
