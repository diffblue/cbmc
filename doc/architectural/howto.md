\ingroup module_hidden
\page cbmc-hacking CBMC Hacking HOWTO

\author Kareem Khazem

This is an introduction to hacking on the `cprover` codebase.  It is not
intended as a user guide to `CBMC` or related tools.  It is structured
as a series of programming exercises that aim to acclimatise the reader
to the basic data structures and workflow needed for contributing to
`CBMC`.


## Initial setup

Clone the [CBMC repository][cbmc-repo] and build it:

    git clone https://github.com/diffblue/cbmc.git
    cd cbmc/src
    make minisat2-download
    make

Ensure that [graphviz][graphviz] is installed on your system (in
particular, you should be able to run a program called `dot`).  Install
[Doxygen][doxygen] and generate doxygen documentation:

    # In the src directory
    doxygen doxyfile
    # View the documentation in a web browser
    firefox doxy/html/index.html

If you've never used doxygen documentation before, get familiar with the
layout.  Open the generated HTML page in a web browser; search for the
class `goto_programt` in the search bar, and jump to the documentation
for that class; and read through the copious documentation.

The build writes executable programs into several of the source
directories.  In this tutorial, we'll be using binaries inside the
`cbmc`, `goto-instrument`, and `goto-cc` directories.  Add these
directories to your `$PATH`:

    # Assuming you cloned CBMC into ~/code
    export PATH=~/code/cbmc/src/goto-instrument:~/code/cbmc/src/goto-cc:~/code/cbmc/src/cbmc:$PATH
    # Add to your shell's startup configuration file so that you don't have to run that command every time.
    echo 'export PATH=~/code/cbmc/src/goto-instrument:~/code/cbmc/src/goto-cc:~/code/cbmc/src/cbmc:$PATH' >> .bashrc

Optional: install an image viewer that can read images on stdin.
I use [feh][feh].

[cbmc-repo]:  https://github.com/diffblue/cbmc/
[doxygen]:    http://www.stack.nl/~dimitri/doxygen/
[graphviz]:   http://www.graphviz.org/
[feh]:        https://feh.finalrewind.org/



## Whirlwind tour of the tools

CBMC's code is located under the `cbmc` directory.  Even if you plan to
contribute only to CBMC, it is important to be familiar with several
other of cprover's auxiliary tools.


### Compiling with `goto-cc`

There should be an executable file called `goto-cc` in the `goto-cc`
directory; make a symbolic link to it called `goto-gcc`:

    cd cbmc/src/goto-cc
    ln -s "$(pwd)/goto-cc" goto-gcc

Find or write a moderately-interesting C program; we'll call it `main.c`.
Run the following commands:

    goto-gcc -o main.goto main.c
    cc -o main.exe main.c

Invoke `./main.goto` and `./main.exe` and observe that they run identically.
The version that was compiled with `goto-gcc` is larger, though:

    du -hs *.{goto,exe}

Programs compiled with `goto-gcc` are mostly identical to their `clang`-
or `gcc`-compiled counterparts, but contain additional object code in
cprover's intermediate representation.  The intermediate representation
is (informally) called a *goto-program*.


### Viewing goto-programs

`goto-instrument` is a Swiss army knife for viewing goto-programs and
performing single program analyses on them.  Run the following command:

    goto-instrument --show-goto-functions main.goto

Many of the instructions in the goto-program intermediate representation
are similar to their C counterparts.  `if` and `goto` statements replace
structured programming constructs.

Find or write a small C program (2 or 3 functions, each containing a few
varied statements).  Compile it using `goto-gcc` as above into an object
file called `main`.  If you installed `feh`, try the following command
to dump a control-flow graph:

    goto-instrument --dot main | tail -n +2 | dot -Tpng | feh -

If you didn't install `feh`, you can write the diagram to the file and
then view it:

    goto-instrument --dot main | tail -n +2 | dot -Tpng > main.png
    Now open main.png with an image viewer

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

    $ goto-instrument --greet main
    hello, world!
    $ goto-instrument --greet Leperina main
    hello, Leperina!

You will also need to add the `greet` option to the
`goto_instrument_parse_options.h` file in order for this to work.
Notice that in the `.h` file, options that take an argument are followed
by a colon (like `(property):`), while simple switches have no colon.
Make sure that you `return 0;` after printing the message.
</div>

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

Each goto_programt object contains a list of
\ref goto_program_templatet::instructiont called
`instructions`.  Each instruction has a field called `code`, which has
type \ref codet.

<div class=memdoc>
**Task:** Add a `--pretty-program` switch to `goto-instrument`.  This
switch should use the `codet::pretty()` function to pretty-print every
\ref codet in the entire program.  The strings that `pretty()` generates
for a codet look like this:

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
</div>

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

The fact that the `op0()` child has a `symbol` ID menas that you could
cast it to a `symbol_exprt` (which is a subtype of `exprt`) using the
function `to_symbol_expr`.

<div class=memdoc>
**Task:** Add flags to `goto-instrument` to print out the following information:
* the name of every function that is *called* in the program;
* the value of every constant in the program;
* the value of every symbol in the program.
</div>
