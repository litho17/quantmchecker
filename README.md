## Compile
1. Compile [Z3](https://github.com/Z3Prover/z3)

    1. Compile Java bindings for Z3
    
        `python scripts/mk_make.py --java; cd build
         make`
    2. Copy native libraries into `lib/`
    
        `find z3/build -iname "*.dylib" -print0 | xargs -0 -I {} cp {} lib/`
    
    3. Copy Java bindings `*.jar` into `lib/`
2. Download and unzip [Checker framework](https://checkerframework.org/manual/#installation). Set checker/dist/*.jar as project libraries.
3. Configure the following paths in `run.sh`
    1. Set `scala_lib` to the path to `scala-library.jar`
    2. Set `checker_framework_bin` to the path of `checker/bin`
    
#### Dependencies
- [Checker framework](https://checkerframework.org/manual/#installation)
- [Z3](https://github.com/Z3Prover/z3)


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
    1. `path_to_checker_jar` with the absolute path to the jar created in the prepreation step (e.g. `${env.HOME}/Desktop/qc.jar`).
    2. `path_to_z3_jar` with the absolute path to the jar created in the prepreation step (e.g. `${env.HOME}/Documents/workspace/z3/build/com.microsoft.z3.jar`)
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
      <groupId>plv.colorado.edu.quantmchecker</groupId>
      <artifactId>qc</artifactId>
      <version>1.0</version>
      <scope>system</scope>
      <systemPath>path_to_checker_jar</systemPath>
    </dependency>
    <dependency>
        <groupId>com.regblanc</groupId>
        <artifactId>scala-smtlib_2.12</artifactId>
        <version>0.2.2</version>
    </dependency>
    <dependency>
      <groupId>com.microsoft</groupId>
      <artifactId>z3</artifactId>
      <version>1.0</version>
      <scope>system</scope>
      <systemPath>path_to_z3_jar</systemPath>
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