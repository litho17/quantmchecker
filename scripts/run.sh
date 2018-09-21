#!/bin/sh

# MAKE SURE THAT JAVAC WITHOUT -PROCESSOR WON'T ISSUE ERRORS

# ==========================Please configure the following paths============================
scala_lib="$HOME/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar"
scala_smtlib="$HOME/.ivy2/cache/com.regblanc/scala-smtlib_2.12/jars/scala-smtlib_2.12-0.2.2.jar"
checker_framework_bin="$HOME/Documents/workspace/checker-framework-2.4.0/checker/bin"
quantmchecker="$HOME/Documents/workspace/quantmchecker"
lib="$quantmchecker/lib"
tool_path="$HOME/Desktop/qc.jar"
external_lib=`python $quantmchecker/scripts/findlibs.py "$1"` # absolute path 
# ==========================================================================================

#javac -cp .:/Users/lumber/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar -AprintErrorStack -processor plv.colorado.edu.quantmchecker.QuantmChecker ~/Documents/workspace/quantmchecker/src/test/java/unit/MotivatingExample.java


export PATH=$checker_framework_bin:$PATH
export LD_LIBRARY_PATH=$lib:$LD_LIBRARY_PATH
export DYLD_LIBRARY_PATH=$lib:$DYLD_LIBRARY_PATH

internal_lib=`python $quantmchecker/scripts/findlibs.py "$lib"`

src_dir="$2" # absolute path

rm -rf output/
mkdir output/

#set -x
classpath=".:$internal_lib:$external_lib:$scala_lib:$scala_smtlib:$tool_path"
javac -Xmaxwarns 10000 -Xmaxerrs 10000 -cp $classpath -AprintErrorStack -processor plv.colorado.edu.quantmchecker.QuantmChecker `find $src_dir -name "*.java"` -d output/

#-AignoreRawTypeArguments
