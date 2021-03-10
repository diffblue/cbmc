\ingroup module_hidden
\page tutorial Tutorials

\section cbmc_tutorial CBMC Developer Tutorial

\tableofcontents

\author Kareem Khazem

This is an introduction to hacking on the `cprover` codebase.  It is not
intended as a user guide to `CBMC` or related tools.  It is structured
as a series of programming exercises that aim to acclimatise the reader
to the basic data structures and workflow needed for contributing to
`CBMC`.


## Initial setup

Clone the [CBMC repository][cbmc-repo] and build it. The build instructions are
written in a file called COMPILING.md in the top level of the repository. I
recommend that you build using CMake---this will place all of the CBMC tools in
a single directory, which you can add to your `$PATH`. For example, if you built
the codebase with the following two commands at the top level of the repository:

    cmake -DCMAKE_BUILD_TYPE=Debug                  \
          -DCMAKE_CXX_COMPILER=/usr/bin/clang++     \
          -DCMAKE_C_COMPILER=/usr/bin/clang         \
          -B build -S .
    cmake --build build

then all the CBMC binaries will be built into `build/bin`, and you can run the
following commands to make CBMC invokable from your terminal.

    # Assuming you cloned CBMC into ~/code
    export PATH=~/code/cbmc/build/bin:$PATH
    # Add to your shell's startup configuration file so that you don't have to run that command every time.
    echo 'export PATH=~/code/cbmc/build/bin:$PATH' >> .bashrc

If you are using Make instead of CMake, the built binaries will be
scattered throughout the source tree. This tutorial uses the binaries
`src/cbmc/cbmc`, `src/goto-instrument/goto-instrument`, and
`src/goto-cc/goto-gcc`, so you will need to add each of those
directories to your `$PATH`, or symlink to those binaries from a
directory that is already in your `$PATH`.

Ensure that [graphviz][graphviz] is installed on your system (in
particular, you should be able to run a program called `dot`).  Install
[Doxygen][doxygen] and generate doxygen documentation:

    # In the src directory
    doxygen doxyfile
    # View the documentation in a web browser
    firefox ~/code/cbmc/doc/html/index.html

If you've never used doxygen documentation before, get familiar with the
layout.  Open the generated HTML page in a web browser; search for the
class `goto_programt` in the search bar, and jump to the documentation
for that class; and read through the copious documentation.

[cbmc-repo]:  https://github.com/diffblue/cbmc/
[doxygen]:    http://www.stack.nl/~dimitri/doxygen/
[graphviz]:   http://www.graphviz.org/


## Whirlwind tour of the tools

CBMC's code is located under the `src` directory.  Even if you plan to
contribute only to CBMC, it is important to be familiar with several
other of cprover's auxiliary tools.


### Compiling with `goto-cc`

If you built using CMake on Unix, you should be able to run the
`goto-gcc` command.
Find or write a moderately-interesting C program; we'll call it `main.c`.
Run the following commands:

    goto-gcc -o main.gb main.c
    cc -o main.exe main.c

Invoke `./main.gb` and `./main.exe` and observe that they run identically.
The version that was compiled with `goto-gcc` is larger, though:

    du -hs *.{goto,exe}

Programs compiled with `goto-gcc` are mostly identical to their `clang`-
or `gcc`-compiled counterparts, but contain additional object code in
cprover's intermediate representation.  The intermediate representation
is (informally) called a *goto-program*.


### Viewing goto-programs

`goto-instrument` is a Swiss army knife for viewing goto-programs and
performing single program analyses on them.  Run the following command:

    goto-instrument --show-goto-functions main.gb

Many of the instructions in the goto-program intermediate representation
are similar to their C counterparts.  `if` and `goto` statements replace
structured programming constructs.

Find or write a small C program (2 or 3 functions, each containing a few
varied statements).  Compile it using `goto-gcc` as above into an object
file called `main`. You can write the diagram to a file and then view it:

    goto-instrument --dot main.gb | tail -n +2 | dot -Tpng > main.png
    open main.png

(the invocation of `tail` is used to filter out the first line of
`goto-instrument` output.  If `goto-instrument` writes more or less
debug output by the time you read this, read the output of
`goto-instrument --dot main` and change the invocation of `tail`
accordingly.)

There are a few other views of goto-programs.  Run `goto-instrument -h`
and try the various switches under the "Diagnosis" section.



## Learning about goto-programs

In this section, you will learn about the basic goto-program data
structures.  Reading from and manipulating these data structures form
the core of writing an analysis for CBMC.


### First steps with `goto-instrument`

<div class=memdoc>
**Task:** Write a simple C program with a few functions, each containing
a few statements.  Compile the program with `goto-gcc` into a binary
called `main`.
</div>


The entry point of `goto-instrument` is in `goto_instrument_main.cpp`.
Follow the control flow into `goto_instrument_parse_optionst::doit()`, located in `goto_instrument_parse_options.cpp`.
At some point in that function, there will be a long sequence of `if` statements.

<div class=memdoc>
**Task:** Add a `--greet` switch to `goto-instrument`, taking an optional
argument, with the following behaviour:
</div>

    $ goto-instrument --greet main.gb
    hello, world!
    $ goto-instrument --greet Leperina main
    hello, Leperina!

You will also need to add the `greet` option to the
`goto_instrument_parse_options.h` file in order for this to work.
Notice that in the `.h` file, options that take an argument are followed
by a colon (like `(property):`), while simple switches have no colon.
Make sure that you `return 0;` after printing the message.

The idea behind `goto-instrument` is that it parses a goto-program and
then performs one single analysis on that goto-program, and then
returns.  Each of the switches in  `doit` function of
`goto_instrument_parse_options` does something different with the
goto-program that was supplied on the command line.


### Goto-program basics

At this point in `goto-instrument_parse_options` (where the `if`
statements are), the goto-program will have been loaded into the object
`goto_functions`, of type `goto_functionst`.  This has a field called
`function_map`, a map from function names to functions.


<div class="memdoc">
**Task:** Add a `--print-function-names` switch to `goto-instrument`
that prints out the name of every function in the goto-binary.  Are
there any functions that you didn't expect to see?
</div>

The following is quite difficult to follow from doxygen, but: the value
type of `function_map` is `goto_function_templatet<goto_programt>`.

<div class=memdoc>
**Task:** Read the documentation for `goto_function_templatet<bodyT>`
and `goto_programt`.
</div>

Each \ref goto_programt object contains a list of
\ref goto_programt::instructiont called
`instructions`.  Each instruction has a field called `code`, which has
type \ref codet.

<div class=memdoc>
**Task:** Add a `--pretty-program` switch to `goto-instrument`.  This
switch should use the `codet::pretty()` function to pretty-print every
\ref codet in the entire program.  The strings that `pretty()` generates
for a codet look like this:
</div>

    index
      * type: unsignedbv
          * width: 8
          * #c_type: char
      0: symbol
          * type: array
              * size: nil
                  * type:
              * #source_location:
                * file: src/main.c
                * line: 18
                * function:
                * working_directory: /some/dir
              0: unsignedbv
                  * width: 8
                  * #c_type: char
    ...

The sub-nodes of a particular node in the pretty representation are
numbered, starting from 0.  They can be accessed through the `op0()`,
`op1()` and `op2()` methods in the `exprt` class.

Every node in the pretty representation has an identifier, accessed
through the `id()` function.  The file `util/irep_ids.def` lists the
possible values of these identifiers; have a quick scan through that
file.  In the pretty representation above, the following facts are true
of that particular node:

  - `node.id() == ID_index`
  - `node.type().id() == ID_unsignedbv`
  - `node.op0().id() == ID_symbol`
  - `node.op0().type().id() == ID_array`

The fact that the `op0()` child has a `symbol` ID means that you could
cast it to a `symbol_exprt` (which is a subtype of `exprt`) using the
function `to_symbol_expr`.

<div class=memdoc>
**Task:** Add flags to `goto-instrument` to print out the following information:
</div>
* the name of every function that is *called* in the program;
* the value of every constant in the program;
* the value of every symbol in the program.
