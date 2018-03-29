#!/bin/sh

# MAKE SURE THAT JAVAC WITHOUT -PROCESSOR WON'T ISSUE ERRORS

# ==========================Please configure the following paths============================
scala_lib="$HOME/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar"
scala_parser_lib="$HOME/.ivy2/cache/org.scala-lang.modules/scala-parser-combinators_2.12/bundles/scala-parser-combinators_2.12-1.1.0.jar"
scalaz3_lib="`pwd`/lib/scalaz3_2.12-3.0.jar"
checker_framework_bin="$HOME/Documents/workspace/checker-framework-2.4.0/checker/bin"
# ==========================================================================================

#javac -cp .:/Users/lumber/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar -AprintErrorStack -processor plv.colorado.edu.quantmchecker.QuantmChecker ~/Documents/workspace/quantmchecker/src/test/java/unit/MotivatingExample.java

external_lib=`python scripts/findlibs.py "$1"` # absolute path

LIB=$(pwd)/lib
export PATH=$checker_framework_bin:$PATH
export LD_LIBRARY_PATH=$LIB:$LD_LIBRARY_PATH
export DYLD_LIBRARY_PATH=$LIB:$DYLD_LIBRARY_PATH


# Jump to the appropriate directory and start annotation processing
pwd=`pwd`
class_files_location="target/scala-2.12/classes"
cd $class_files_location
src_dir="$pwd/$2" # relative path

mkdir output/

# set -x
fully_qualified_name_prefix="plv.colorado.edu."
QUANTMCHECKER="quantmchecker.QuantmChecker"
LISTADDCHECKER="listaddchecker.ListaddChecker"

classpath=".:$external_lib:$scala_lib:$scala_parser_lib:$scalaz3_lib"
javac -cp $classpath -AprintErrorStack -processor $fully_qualified_name_prefix$QUANTMCHECKER `find $src_dir -name "*.java"` -d output/

#-AignoreRawTypeArguments
