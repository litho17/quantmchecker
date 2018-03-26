#!/bin/sh

export PATH=$HOME/Documents/workspace/checker-framework-2.4.0/checker/bin:$PATH

#javac -cp .:/Users/lumber/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar -AprintErrorStack -processor plv.colorado.edu.quantmchecker.QuantmChecker ~/Documents/workspace/quantmchecker/src/test/java/unit/MotivatingExample.java

scala_lib="$HOME/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar"
class_files_location="target/scala-2.12/classes"
fully_qualified_name="plv.colorado.edu."
QUANTMCHECKER="quantmchecker.QuantmChecker"
LISTADDCHECKER="listaddchecker.ListaddChecker"

# MAKE SURE THAT JAVAC WITHOUT -PROCESSOR WON'T ISSUE ERRORS

pwd=`pwd`
cd $class_files_location
if [ $1 == '1' ]
then
#	set -x
	javac -cp .:$scala_lib -AprintErrorStack -processor $fully_qualified_name$QUANTMCHECKER $pwd/$2
elif [ $1 == '2' ]
then
#	set -x
	javac -cp .:$scala_lib -AprintErrorStack -processor $fully_qualified_name$LISTADDCHECKER $pwd/$2
else
	echo "Which checker to run? Please choose 1 or 2"
fi
#-AignoreRawTypeArguments
