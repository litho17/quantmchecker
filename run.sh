#!/bin/sh

export PATH=$HOME/Documents/workspace/checker-framework-2.4.0/checker/bin:$PATH

#javac -cp .:/Users/lumber/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar -AprintErrorStack -processor plv.colorado.edu.quantmchecker.QuantmChecker ~/Documents/workspace/quantmchecker/src/test/java/unit/MotivatingExample.java

class_files_location="target/scala-2.12/classes"

fully_qualified_name_prefix="plv.colorado.edu."
QUANTMCHECKER="quantmchecker.QuantmChecker"
LISTADDCHECKER="listaddchecker.ListaddChecker"

# MAKE SURE THAT JAVAC WITHOUT -PROCESSOR WON'T ISSUE ERRORS

lib_path=`python scripts/findlibs.py "$1"` # absolute path
#echo $lib_path

scala_lib="$HOME/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar"
scala_parser_lib="$HOME/.ivy2/cache/org.scala-lang.modules/scala-parser-combinators_2.12/bundles/scala-parser-combinators_2.12-1.1.0.jar"
classpath=".:$lib_path:$scala_lib:$scala_parser_lib"


pwd=`pwd`
cd $class_files_location
src_dir="$pwd/$2" # relative path

mkdir output/

#	set -x
javac -cp $classpath -AprintErrorStack -processor $fully_qualified_name_prefix$QUANTMCHECKER `find $src_dir -name "*.java"` -d output/

#-AignoreRawTypeArguments
