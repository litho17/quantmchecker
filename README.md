## Compile
1. Compile [Scala Z3](https://github.com/epfl-lara/ScalaZ3)

    1. Copy native libraries into `lib/`
    
        `find ScalaZ3/ -iname "*.dylib" -print0 | xargs -0 -I {} cp {} lib/`
    
    2. Copy `scalaz3_2.12-3.0.jar` into `lib/`
2. Download and unzip [Checker framework](https://checkerframework.org/manual/#installation). Set checker/dist/*.jar as project libraries.
3. Configure the following paths in `run.sh`
    1. Set `scala_lib` to the path to `scala-library.jar`
    2. Set `scala_parser_lib` to the path to `scala-parser-combinators_2.12-1.1.0.jar`
    3. Set `scalaz3_lib` to `lib/scalaz3_2.12-3.0.jar`
    4. Set `checker_framework_bin` to the path of `checker/bin`
4. Build and install lpsolver
     1. Download `lp_solve_5.5.2.5_java.zip` and `lp_solve_5.5.2.5_source.tar.gz` from http://lpsolve.sourceforge.net/5.5/
     2. Build native library
         1. Unzip `lp_solve_5.5.2.5_source.tar.gz`
         2. `cd lp_solve_5.5/lpsolve55`
         3. `sh ccc.osx` 
         4. The output will be `liblpsolve55.dylib` and `liblpsolve55.a` under directory `lp_solve_5.5/lpsolve55/bin/`. Copy them to some place (e.g. `path_to_native/`)
     3. Build Java bindings
         1. Unzip `lp_solve_5.5.2.5_java.zip`
         2. Configure `lib/mac/build-osx`
            1. Set `LPSOLVE_DIR` to the path of t
            2. Set `JDK_DIR` to the directory of jdk (e.g. On Mac, it will look like `/Library/Java/JavaVirtualMachines/jdk1.8.0_121.jdk/Contents/Home/include`)
            3. Set `JDK_DIR2` to the directory that contains `jni_md.h` and add `-I $JDK_DIR2` to the line that sets `INCL` (e.g. On Mac, it will look like `/Library/Java/JavaVirtualMachines/jdk1.8.0_121.jdk/Contents/Home/include/darwin`)
            4. Add `-Lpath_to_native/` to the line that links the library `-llpsolve55`
            5. Run `build-osx`
            6. The output will be `liblpsolve55j.jnilib`. Rename it as `liblpsolve55j.dylib`
     4. Copy `lpsolve55j.jar` (from `lp_solve_5.5.2.5_java/`), `liblpsolve55.dylib`, `liblpsolve55.a` and `liblpsolve55j.dylib` into `lib/`
     5. Note: The above steps are for unfortunate people who use Mac OS (me as well). Otherwise, if you are using Linux or Windows, you will only need to follow instructions in section "Using lpsolve from Java" on [this](http://lpsolve.sourceforge.net/5.5/) website
5. Install Java ILP

    Copy `javailp-1.2a.jar` into `lib/`
    
#### Dependencies
- [Scala Parser Combinator](https://github.com/scala/scala-parser-combinators)
- [Scala Z3](https://github.com/epfl-lara/ScalaZ3)
- [Checker framework](https://checkerframework.org/manual/#installation)
- [lpsolver](http://lpsolve.sourceforge.net/5.5/)
- [Java ILP](http://javailp.sourceforge.net/)


## Intergrate with building systems

#### Prepration step
1. Compile the checker into class files
2. Setup and run `./scripts/setup.sh` to set up the environment variables and create a jar file containing the class files.

    1. Set `checkerdir` to the absolute path of the source code root directory of the customized checker
    2. The created jar file is by default on the desktop, named as `qc.jar`

#### Maven

1. Add the following content into `<properties></properties>` section in pom.xml
    ```xml
     <annotatedJdk>${org.checkerframework:jdk8:jar}</annotatedJdk>
     ```
2. Add the following content into `<dependencies></dependencies>` section in pom.xml.

    Note, please replace
    1.  `path_to_scalaz3_lib_jar` with the absolute path to the jar file of scalaz3 (e.g. `${env.HOME}/Documents/workspace/quantmchecker/lib/scalaz3_2.12-3.0.jar`)
    2. `path_to_checker_jar` with the absolute path the the jar created in the prepreation step (e.g. `${env.HOME}/Desktop/qc.jar`).
    ```xml
    <!-- Annotations from the Checker Framework: nullness, interning, locking, ... -->
    <dependency>
      <groupId>org.checkerframework</groupId>
      <artifactId>checker-qual</artifactId>
      <version>2.5.1</version>
    </dependency>
    <dependency>
      <groupId>org.checkerframework</groupId>
      <artifactId>checker</artifactId>
      <version>2.5.1</version>
    </dependency>
    <!-- The annotated JDK to use. -->
    <dependency>
      <groupId>org.checkerframework</groupId>
      <artifactId>jdk8</artifactId>
      <version>2.5.1</version>
    </dependency>
    <dependency>
      <groupId>org.scala-lang</groupId>
      <artifactId>scala-library</artifactId>
      <version>2.12.1</version>
    </dependency>
    <dependency>
      <groupId>org.scala-lang.modules</groupId>
      <artifactId>scala-parser-combinators_2.12</artifactId>
      <version>1.1.0</version>
    </dependency>
    <dependency>
      <groupId>epfl-lara</groupId>
      <artifactId>scalaz3</artifactId>
      <version>3.0</version>
      <scope>system</scope>
      <systemPath>path_to_scalaz3_lib_jar</systemPath>
    </dependency>
    <dependency>
      <groupId>plv.colorado.edu.quantmchecker</groupId>
      <artifactId>qc</artifactId>
      <version>1.0</version>
      <scope>system</scope>
      <systemPath>path_to_checker_jar</systemPath>
    </dependency>
    ```
3. Add the following in to `<build><plugins></plugins></build>` section in pom.xml

    Note, please replace `name_of_checker` with name of the checker (e.g. `plv.colorado.edu.quantmchecker.QuantmChecker`).
    ```xml
    <plugin>
      <!-- This plugin will set properties values using dependency information -->
      <groupId>org.apache.maven.plugins</groupId>
      <artifactId>maven-dependency-plugin</artifactId>
      <executions>
        <execution>
          <goals>
            <goal>properties</goal>
          </goals>
        </execution>
      </executions>
    </plugin>
    <plugin>
      <groupId>org.apache.maven.plugins</groupId>
      <artifactId>maven-compiler-plugin</artifactId>
      <version>3.6.1</version>
      <configuration>
        <source>1.8</source>
        <target>1.8</target>
        <compilerArguments>
          <Xmaxerrs>10000</Xmaxerrs>
          <Xmaxwarns>10000</Xmaxwarns>
        </compilerArguments>
        <annotationProcessors>
          <!-- Add all the checkers you want to enable here -->
          <annotationProcessor>name_of_checker</annotationProcessor>
        </annotationProcessors>
        <compilerArgs>
          <arg>-AprintErrorStack</arg>
          <!-- location of the annotated JDK, which comes from a Maven dependency -->
          <arg>-Xbootclasspath/p:${annotatedJdk}</arg>
          <!-- Uncomment the following line to turn type-checking warnings into errors. -->
          <!-- <arg>-Awarns</arg> -->
        </compilerArgs>
      </configuration>
    </plugin>
    ```