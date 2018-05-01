checkerdir="$HOME/Documents/workspace/quantmchecker"
checkerlib="$checkerdir/lib"
checkerclasses="$checkerdir/target/scala-2.12/classes"

scala_lib="$HOME/.sbt/preloaded/org.scala-lang/scala-library/2.12.1/jars/scala-library.jar"
scala_parser_lib="$HOME/.ivy2/cache/org.scala-lang.modules/scala-parser-combinators_2.12/bundles/scala-parser-combinators_2.12-1.1.0.jar"
scalaz3_lib="$checkerlib/scalaz3_2.12-3.0.jar"

checker_framework_bin="$HOME/Documents/workspace/checker-framework-2.4.0/checker/bin"

export PATH=$checker_framework_bin:$PATH
export LD_LIBRARY_PATH=$checkerlib:$LD_LIBRARY_PATH
export DYLD_LIBRARY_PATH=$checkerlib:$DYLD_LIBRARY_PATH

classpath=".:$scala_lib:$scala_parser_lib:$scalaz3_lib:$checkerclasses"

fully_qualified_name_prefix="plv.colorado.edu."
QUANTMCHECKER="quantmchecker.QuantmChecker"


javac -Xmaxwarns 10000 -Xmaxerrs 10000 -cp $classpath -AprintErrorStack -processor $fully_qualified_name_prefix$QUANTMCHECKER
