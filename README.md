# Introduction
This repo contains the tool implementation of the following paper

- Lu, Tianhan, et al. "Type-directed bounding of collections in reactive programs." International Conference on Verification, Model Checking, and Abstract Interpretation. Springer, Cham, 2019. [[PDF]](https://arxiv.org/abs/1810.10443)

This tool is essentially **a third-party type checker for a target Java project**.
It can verify the boundedness of collection-typed variables of every method in the target project via a type checking approach.

In order for this tool to perform verification, the target project needs to be compilable and properly annotated. See the above paper for details about what an annotation should look like.

# Setup dependencies
Since this tool relies on external libraries [Checker framework](https://checkerframework.org/manual/#installation) and [Z3](https://github.com/Z3Prover/z3), these libraries need to be compiled and installed on your machine in order to **compile and run** this tool.

- Compile Z3

    1. Compile Java bindings for Z3
    
        ```
        python scripts/mk_make.py --java; cd build
        make
        ```
    2. Copy native libraries into `lib/`. Below is an example for Mac OS.
    
        ```
        find z3/build -iname "*.dylib" -print0 | xargs -0 -I {} cp {} lib/
        ```
    
    3. Copy Java bindings `*.jar` into `lib/`
- Set Checker framework as project libraries of your IDE
	- Set `lib/checker-framework-2.5.5/checker/dist/*.jar` as project libraries
- Install Python
- Edit `scripts/findlibs.py` on Windows
	- Change the delimiter to `;` from `:`
	- This script is used to find all jar files recursively inside a directory and print out a valid string as the parameter to `-classpath`

# Run the tool
There are 2 ways to run the tool, depending on how a target project is compiled

- If the target project is compilable via `javac`, then run a modified version of `javac` and specify this tool as an annotation processor.

	This modified version of `javac` is located at directory `checker/bin/` in the unzipped Checker Framework. In fact, it specifies the Checker framework on the classpath and "redirects all passed arguments to `org.checkerframework.framework.util.CheckerMain`".
- If the target project is compilable via Maven building sytem, then we need to modify the Maven configuration file, in order to specify this tool as an annotation processor.

To run this tool, you should first compile it. Then depending on how the target project is compiled, configure the compiler accordingly. After running the tool, a log file will be generated in the directory `~/Desktop`.

## Compile the tool
1. Compile the source code into class files.
2. Create a jar file containing all class files. Name the jar file as `qc.jar` and put it in the directory `~/Desktop`.

	```
	cd target/scala-x.xx/classes
	jar -cvf qc.jar plv/
	mv qc.jar ~/Desktop
	```

## Javac
1. Configure `scripts/run.sh`
	- Set `scala_lib` to the path of `scala-library.jar`
	- Set `scala_smtlib` to the path  of `scala-smtlib_xxxxxx.jar`
	- Note: If you are using new versions of Mac OS, notice that the setttings of `LD_LIBRARY_PATH` and `DYLD_LIBRARY_PATH` might not take effect, because System Integrity Protection is enabled by defult. To turn it off or check if it is enabled on your machine, check [here](http://osxdaily.com/2015/10/05/disable-rootless-system-integrity-protection-mac-os-x/). [[Reference]](https://github.com/nteract/nteract/issues/1523#issuecomment-284027093)
2. Run `scripts/run.sh target_lib target_src_dir` from the root directory of this project where 
	- `target_lib ` is the path of the libraries necessary for compiling the target project
	- `target_src_dir ` is the path of the directory containing source code of the target project


## Maven
1. Run `scripts/setup.sh` to set up the environment variables. Before running this script, set the values following instruction in Step 1 of Section Javac (when configuring `scripts/run.sh`).
2. Add the following content into `<properties></properties>` section of `pom.xml`.

	```xml
	<annotatedJdk>${org.checkerframework:jdk8:jar}</annotatedJdk>
	```
3. Add the following content into `<dependencies></dependencies>` section of `pom.xml`. Note that you will need to replace
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
3. Add the following in to `<build><plugins></plugins></build>` section of `pom.xml`.

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

# Run the benchmarks
1. Setup dependencies as described above
2. Run `./scripts/stac.sh` and `./scripts/benchmark.sh`