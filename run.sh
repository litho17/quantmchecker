#!/bin/sh

# MAKE SURE THAT JAVAC WITHOUT -PROCESSOR WON'T ISSUE ERRORS

# ==========================Please configure the following paths============================
scala_lib="$HOME/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar"
scala_smtlib="$HOME/.ivy2/cache/com.regblanc/scala-smtlib_2.12/jars/scala-smtlib_2.12-0.2.2.jar"
checker_framework_bin="$HOME/Documents/workspace/checker-framework-2.4.0/checker/bin"
# ==========================================================================================

#javac -cp .:/Users/lumber/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar -AprintErrorStack -processor plv.colorado.edu.quantmchecker.QuantmChecker ~/Documents/workspace/quantmchecker/src/test/java/unit/MotivatingExample.java

external_lib=`python scripts/findlibs.py "$1"` # absolute path

LIB=$(pwd)/lib
export PATH=$checker_framework_bin:$PATH
export LD_LIBRARY_PATH=$LIB:$LD_LIBRARY_PATH
export DYLD_LIBRARY_PATH=$LIB:$DYLD_LIBRARY_PATH
internal_lib=`python scripts/findlibs.py "$LIB"`


# Jump to the appropriate directory and start annotation processing
pwd=`pwd`
class_files_location="target/scala-2.12/classes"
cd $class_files_location
src_dir="$pwd/$2" # relative path

rm -rf output/
mkdir output/

# set -x
QUANTMCHECKER="plv.colorado.edu.quantmchecker.QuantmChecker"

classpath=".:$internal_lib:$external_lib:$scala_lib:$scala_smtlib"
javac -Xmaxwarns 10000 -Xmaxerrs 10000 -cp $classpath -AprintErrorStack -processor $QUANTMCHECKER `find $src_dir -name "*.java"` -d output/

#-AignoreRawTypeArguments
