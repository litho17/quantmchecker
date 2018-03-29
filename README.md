### Installation
1. Compile [Scala Z3](https://github.com/epfl-lara/ScalaZ3)

    1. Copy native libraries into `lib/`
    
        `find ScalaZ3/ -iname "*.dylib" -print0 | xargs -0 -I {} cp {} lib/`
    
    2. Copy `scalaz3_2.12-3.0.jar` into `lib/`
2. Download and unzip [Checker framework](https://checkerframework.org/manual/#installation)
3. Configure the following paths in `run.sh`
    1. Set `scala_lib` to the path to `scala-library.jar`
    2. Set `scala_parser_lib` to the path to `scala-parser-combinators_2.12-1.1.0.jar`
    3. Set `scalaz3_lib` to `lib/scalaz3_2.12-3.0.jar`
    4. Set `checker_framework_bin` to the path of `checker/bin`
    
### Dependencies
- [Scala Parser Combinator](https://github.com/scala/scala-parser-combinators)
- [Scala Z3](https://github.com/epfl-lara/ScalaZ3)
- [Checker framework](https://checkerframework.org/manual/#installation)