Each sub directory inside this one contains class files which have been compiled
with specific java compilers. The procedure taken to produce these files is as
follows -
 1. Install the java compilers of interest. Skip this step if you already have
 them installed.
 2. Use `sudo update-alternatives --config javac` to configure your system to
 use the compiler of interest.
 3. Use `javac -version` to confirm the desired compilier has been correctly
 configured. The version information for each compiler is as follows -
    * openJdk 8     - 1.8.0_151
    * oracle java 8 - 1.8.0_161
    * oracle java 9 - 9.0.4
 4. Compile the `.java` files using `javac -g ./*.java`. The `-g` flag switches
 on debugging output, which we require.
 5. The `.class` files should have been written to the current directory. They
 can now be moved into the appropriate sub directory. For example -
 `mkdir my_compiler_classes && mv ./*.class ./my_compiler_classes`
 6. If this is a new compiler, add it to the test, by adding the compilier to
 the list in the `run_test_with_compilers` function in
 `java_bytecode_parse_lambda_method_table.cpp`.
 7. Repeat steps 2 through 6 for each additional compiler.

The procedure for compiling with Eclipse is different. Installing the java
Eclipse IDE does not setup a version of javac command. So to produce the class
files for Eclipse, the procedure is as follows -
 1. Open Eclipse IDE.
 2. Create new project.
 3. Import the `.java` files into the project, using the "General->File System"
 import source.
 4. The `.java` files should now show in the src folder of the package explorer.
 The IDE will have automatically compiled these, because it needs the `.class`
 files for its autocomplete/syntax highlighting/tool tip functionality.
 5. The auto compiled files should be in a `bin` sub directory of the project
 directory. These can be copied into the appropriate sub directory of the unit
 test using your command line shell or file browser of choice. Note that the
 `bin` directory and the class files are not shown in the Eclipse IDE.

The Eclipse java compiler is distibuted as a .jar file, which can be run from
the command line. For detailed information see here [https://help.eclipse.org/neon/index.jsp?topic=%2Forg.eclipse.jdt.doc.user%2Ftasks%2Ftask-using_batch_compiler.htm]
For example the eclipse compiler version could be extracted with `java -jar
./ecj-4.7.2.jar -version`. However this is redundant as the version number is
usually in the file name of the jar file already. The java files can be compiled
with the eclipse compiler through the command line with `java -jar
./ecj-4.7.2.jar -g -1.8 ./*.java`. The additional `-1.8` is required to use java
compilance level 1.8, which is required for lambdas.
