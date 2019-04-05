#!/bin/sh

# ==========================Please configure the following paths============================
quantmchecker="$HOME/Documents/workspace/quantmchecker"
scala_lib="$HOME/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar"
# scala_parser_lib="$HOME/.ivy2/cache/org.scala-lang.modules/scala-parser-combinators_2.12/bundles/scala-parser-combinators_2.12-1.1.0.jar"
checker_framework_bin="$HOME/Documents/workspace/checker-framework-2.4.0/checker/bin"
# ==========================================================================================

lib="$quantmchecker/lib"
tool_path="$HOME/Desktop/qc.jar"
scalaz3_lib="$checkerlib/scalaz3_2.12-3.0.jar"

export PATH=$checker_framework_bin:$PATH
export LD_LIBRARY_PATH=$lib:$LD_LIBRARY_PATH
export DYLD_LIBRARY_PATH=$lib:$DYLD_LIBRARY_PATH

classpath=".:$scala_lib:$scalaz3_lib:$tool_path"

fully_qualified_name_prefix="plv.colorado.edu."
QUANTMCHECKER="quantmchecker.QuantmChecker"


javac -Xmaxwarns 10000 -Xmaxerrs 10000 -cp $classpath -AprintErrorStack -processor $fully_qualified_name_prefix$QUANTMCHECKER
