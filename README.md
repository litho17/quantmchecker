# Introduction
This repo contains the tool implementation of the following paper

- Lu, Tianhan, et al. "Type-directed bounding of collections in reactive programs." International Conference on Verification, Model Checking, and Abstract Interpretation. Springer, Cham, 2019. [[PDF]](https://arxiv.org/abs/1810.10443)

This tool is essentially a third-party type checker for a target Java project.
It can verify the boundedness of collection-typed variables of every method in the target project.

In order for this tool to perform verification, the target Java project needs to be compilable and properly annotated. See the above paper for details about what an annotation should look like.

# Compile external libraries
Since this tool relies on external libraries [Checker framework](https://checkerframework.org/manual/#installation) and [Z3](https://github.com/Z3Prover/z3), these libraries need to be compiled and installed on your machine in order to compile this tool. Below are instructions about how to compile/install them.

- Compile Z3

    1. Compile Java bindings for Z3
    
        `python scripts/mk_make.py --java; cd build
         make`
    2. Copy native libraries into `lib/`
    
        `find z3/build -iname "*.dylib" -print0 | xargs -0 -I {} cp {} lib/`
    
    3. Copy Java bindings `*.jar` into `lib/`
- Install Checker framework
	1. Download and unzip [Checker framework](https://checkerframework.org/manual/#installation)
	2. Set `checker/dist/*.jar` as project libraries in your IDE (e.g. Intellij)

# Run the tool
There are 2 ways to run the tool, depending on how a target project is compiled

- If the target project is compilable via `javac`, then run a modified version of `javac` and specify this tool as an annotation processor.
	- This modified version of `javac` is located at directory `checker/bin/` in the unzipped Checker Framework. In fact, it specifies the Checker framework on the classpath and "redirects all passed arguments to `org.checkerframework.framework.util.CheckerMain`".
- If the target project is compilable via Maven building sytem, then we need to modify the Maven configuration file, in order to specify this tool as an annotation processor.

## Javac
1. Configure the following paths in `run.sh`
	1. Set `scala_lib` to the path to `scala-library.jar`
	2. Set `checker_framework_bin` to the path of `checker/bin`
2. Run `run.sh` from the root directory of this project


## Maven
1. Compile the source code into class files.
2. Create a jar file containing all class files. Name the jar file as `qc.jar` and put it in the directory `~/Desktop`.
3. Setup and run `./scripts/setup.sh` to set up the environment variables and create a jar file containing the class files.

	- Inside `setup.sh`, set variable `checkerdir` to the absolute path of the source code root directory of the customized checker
4. Maven configuration
	1. Add the following content into `<properties></properties>` section in pom.xml
    ```xml
     <annotatedJdk>${org.checkerframework:jdk8:jar}</annotatedJdk>
     ```
	2. Add the following content into `<dependencies></dependencies>` section in pom.xml. Note that you will need to replace
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