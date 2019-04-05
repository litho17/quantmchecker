#!/bin/sh

# Precondition before running this script
# - This script is executed from the root directory of this project via `./scripts/setup.sh`

PWD=$(pwd)

# ==========================Please configure the following paths============================
scala_lib="$HOME/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar"
scala_smtlib="$HOME/.ivy2/cache/com.regblanc/scala-smtlib_2.12/jars/scala-smtlib_2.12-0.2.2.jar"
# ==========================================================================================

tool_path="$HOME/Desktop/qc.jar"
lib="$PWD/lib"
checker_framework_bin="$lib/checker-framework-2.5.5/checker/bin"
export PATH=$checker_framework_bin:$PATH
export LD_LIBRARY_PATH=$lib:$LD_LIBRARY_PATH
export DYLD_LIBRARY_PATH=$lib:$DYLD_LIBRARY_PATH

classpath=".:$lib/com.microsoft.z3.jar:$scala_lib:$scala_smtlib:$tool_path"



echo "\n\nVerifying spring-petclinic"
cd src/test/java/spring-petclinic
mvn -e compile

echo "Verifying jrecruiter..."
cd src/test/java/jrecruiter
mvn -e compile

echo "\n\nVerifying jforum3..."
cd src/test/java/jforum3
mvn -e compile
