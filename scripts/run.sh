#!/bin/sh

# Pre-condition before running this script
# - Using javac to compile the target project will not have compiler errors
# - This script is executed from the root directory of this project via `./scripts/run.sh`

PWD=$(pwd)

# ==========================Please configure the following paths============================
scala_lib="$HOME/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar"
scala_smtlib="$HOME/.ivy2/cache/com.regblanc/scala-smtlib_2.12/jars/scala-smtlib_2.12-0.2.2.jar"
# ==========================================================================================

tool_jar="$HOME/Desktop/qc.jar"
target_project_lib=`python $PWD/scripts/findlibs.py "$1"` # absolute path 
src_dir="$2" # absolute path

lib="$PWD/lib"
checker_framework_bin="$lib/checker-framework-2.5.5/checker/bin"
export PATH=$checker_framework_bin:$PATH
export LD_LIBRARY_PATH=$lib:$LD_LIBRARY_PATH
export DYLD_LIBRARY_PATH=$lib:$DYLD_LIBRARY_PATH

rm -rf output/
mkdir output/

# set -x
classpath=".:$lib/com.microsoft.z3.jar:$target_project_lib:$scala_lib:$scala_smtlib:$tool_jar"
javac -Xmaxwarns 10000 -Xmaxerrs 10000 -cp $classpath -AprintErrorStack -processor plv.colorado.edu.quantmchecker.QuantmChecker `find $src_dir -name "*.java"` -d output/

