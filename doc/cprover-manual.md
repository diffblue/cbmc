\ingroup module_hidden
\page cprover-manual CProver User Manual

\author Daniel Kroening

This tutorial is intended for users of CProver (CBMC, SatAbs, and
associated tools).

\tableofcontents

\section man_introduction Introduction

## Motivation

Numerous tools to hunt down functional design flaws in silicon have been
available for many years, mainly due to the enormous cost of hardware
bugs. The use of such tools is wide-spread. In contrast, the market for
tools that address the need for quality software is still in its
infancy.

Research in software quality has an enormous breadth. We focus the
presentation using two criteria:

1.  We believe that any form of quality requires a specific *guarantee*,
    in theory and practice.
2.  The sheer size of software designs requires techniques that are
    highly *automated*.

In practice, quality guarantees usually do not refer to "total
correctness" of a design, as ensuring the absence of all bugs is too
expensive for most applications. In contrast, a guarantee of the absence
of specific flaws is achievable, and is a good metric of quality.

We document two programs that try to achieve formal guarantees of the
absence of specific problems: CBMC and SATABS. The algorithms
implemented by CBMC and SATABS are complementary, and often, one tool is
able to solve a problem that the other cannot solve.

Both CBMC and SATABS are verification tools for ANSI-C/C++ programs.
They verify array bounds (buffer overflows), pointer safety, exceptions
and user-specified assertions. Both tools model integer arithmetic
accurately, and are able to reason about machine-level artifacts such as
integer overflow. CBMC and SATABS are therefore able to detect a class
of bugs that has so far gone unnoticed by many other verification tools.
This manual also covers some variants of CBMC, which includes HW-CBMC
for
\ref man_hard-soft-introduction "hardware/software co-verification".

## Bounded Model Checking with CBMC

CBMC implements a technique called *Bounded Model Checking* (BMC). In
BMC, the transition relation for a complex state machine and its
specification are jointly unwound to obtain a Boolean formula, which is
then checked for satisfiability by using an efficient SAT procedure. If
the formula is satisfiable, a counterexample is extracted from the
output of the SAT procedure. If the formula is not satisfiable, the
program can be unwound more to determine if a longer counterexample
exists.

In many engineering domains, real-time guarantees are a strict
requirement. An example is software embedded in automotive controllers.
As a consequence, the loop constructs in these types of programs often
have a strict bound on the number of iterations. CBMC is able to
formally verify such bounds by means of *unwinding assertions*. Once
this bound is established, CBMC is able to prove the absence of errors.

A more detailed description of how to apply CBMC to verify programs is
\ref man_cbmc-tutorial "here".

## Automatic Program Verification with SATABS

In many cases, lightweight properties such as array bounds do not rely
on the entire program. A large fraction of the program is *irrelevant*
to the property. SATABS exploits this observation and computes an
*abstraction* of the program in order to handle large amounts of code.

In order to use SATABS it is not necessary to understand the abstraction
refinement process. For the interested reader, a high-level introduction
to abstraction refinement is provided
\ref man_satabs-overview "here".
We also provide
\ref man_satabs-tutorials "tutorials on how to use SATABS".

Just as CBMC, SATABS attempts to build counterexamples that refute the
property. If such a counterexample is found, it is presented to the
engineer to facilitate localization and repair of the program.

### Example: Buffer Overflows

In order to give a brief overview of the capabilities of CBMC and SATABS
we start with a small example. The issue of *[buffer
overflows](http://en.wikipedia.org/wiki/Buffer_overflow)* has obtained
wide public attention. A buffer is a contiguously-allocated chunk of
memory, represented by an array or a pointer in C. Programs written in C
do not provide automatic bounds checking on the buffer, which means a
program can – accidentally or maliciously – write past a buffer. The
following example is a perfectly valid C program (in the sense that a
compiler compiles it without any errors):

```{.c}
int main()
{
  int buffer[10];
  buffer[20] = 10;
}
```

However, the write access to an address outside the allocated memory
region can lead to unexpected behavior. In particular, such bugs can be
exploited to overwrite the return address of a function, thus enabling
the execution of arbitrary user-induced code. CBMC and SATABS are able
to detect this problem and reports that the "upper bound property" of
the buffer is violated. CBMC and SATABS are capable of checking these
lower and upper bounds, even for arrays with dynamic size. A detailed
discussion of the properties that CBMC and SATABS can check
automatically is \ref man_instrumentation-properties "here".

## Hardware/Software Co-Verification

Software programs often interact with hardware in a non-trivial manner,
and many properties of the overall design only arise from the interplay
of both components. CBMC and SATABS therefore support *Co-Verification*,
i.e., are able to reason about a C/C++ program together with a circuit
description given in Verilog.

These co-verification capabilities can also be applied to perform
refinement proofs. Software programs are often used as high-level
descriptions of circuitry. While both describe the same functionality,
the hardware implementation usually contains more detail. It is highly
desirable to establish some form for equivalence between the two
descriptions. Hardware/Software co-verification and equivalence checking
with CBMC and SATABS are described
\ref man_hard-soft-introduction "here".


\section man_installation Installation

\subsection man_install-cbmc Installing CBMC

### Requirements

CBMC is available for Windows, i86 Linux, and MacOS X. CBMC requires a
code pre-processing environment comprising of a suitable preprocessor
and an a set of header files.

1.  **Linux:** the preprocessor and the header files typically come with
    a package called *gcc*, which must be installed prior to the
    installation of CBMC.

2.  **Windows:** The Windows version of CBMC requires the preprocessor
    `cl.exe`, which is part of Microsoft Visual Studio. We recommend the
    free [Visual Studio Community
    2013](http://www.visualstudio.com/en-us/products/visual-studio-community-vs).

3.  **MacOS:** Install the [XCode Command Line
    Utilities](http://developer.apple.com/technologies/xcode.html) prior
    to installing CBMC. Just installing XCode alone is not enough.

Important note for Windows users: Visual Studio's `cl.exe` relies on a
complex set of environment variables to identify the target architecture
and the directories that contain the header files. You must run CBMC
from within the *Visual Studio Command Prompt*.

Note that the distribution files for the [Eclipse
plugin](installation-plugin.shtml) include the CBMC executable.
Therefore, if you intend to run CBMC exclusively within Eclipse, you can
skip the installation of the CBMC executable. However, you still have to
install the compiler environment as described above.

### Installing the CBMC Binaries

1.  Download CBMC for your operating system. The binaries are available
    from http://www.cprover.org/cbmc/.
2.  Unzip/untar the archive into a directory of your choice. We
    recommend to add this directory to your `PATH` environment variable.

You are now ready to \ref man_cbmc-tutorial "use CBMC"!

### Building CBMC from Source

Alternatively, the CBMC source code is available [via
SVN](http://www.cprover.org/svn/cbmc/). To compile the source code,
follow [these
instructions](http://www.cprover.org/svn/cbmc/trunk/COMPILING).

\subsection man_install-satabs Installing SATABS

### Requirements

SATABS is available for Windows, i86 Linux, and MacOS X. SATABS requires
a code pre-processing environment comprising of a suitable preprocessor
and an a set of header files.

1.  **Linux:** the preprocessor and the header files typically come with
    a package called *gcc*, which must be installed prior to the
    installation of SATABS.
2.  **Windows:** The Windows version of SATABS requires the preprocessor
    `cl.exe`, which is part of Visual Studio (including the free [Visual
    Studio
    Express](http://msdn.microsoft.com/vstudio/express/visualc/)).
3.  **MacOS:** Install
    [XCode](http://developer.apple.com/technologies/xcode.html) prior to
    installing SATABS.

Important note for Windows users: Visual Studio's `cl.exe` relies on a
complex set of environment variables to identify the target architecture
and the directories that contain the header files. You must run SATABS
from within the *Visual Studio Command Prompt*.

Note that the distribution files for the [Eclipse
plugin](installation-plugin.shtml) include the command-line tools.
Therefore, if you intend to run SATABS exclusively within Eclipse, you
can skip the installation of the command-line tools. However, you still
have to install the compiler environment as described above.

### Choosing and Installing a Model Checker

You need to install a Model Checker in order to be able to run SATABS.
You can choose between following alternatives:

-   **Cadence SMV**. Available from http://www.kenmcmil.com/smv.html.
    Cadence SMV is a commercial model checker. The free version that is
    available on the homepage above must not be used for commercial
    purposes (read the license agreement thoroughly before you download
    the tool). The documentation for SMV can be found in the directory
    where you unzip/untar SMV under ./smv/doc/smv/. Read the
    installation instructions carefully. The Linux/MacOS versions
    require setting environment variables. You must add add the
    directory containing the `smv` binary (located in ./smv/bin/,
    relative to the path where you unpacked it) to your `PATH`
    environment variable. SATABS uses Cadence SMV by default.

-   **NuSMV**. Available from http://nusmv.irst.itc.it/. NuSMV is the
    open source alternative to Cadence SMV. Installation instructions
    and documentation can be found on the NuSMV homepage. The directory
    containing the NuSMV binary should be added to your `PATH`
    environment variable. Use the option

        --modelchecker nusmv

    to instruct SATABS to use NuSMV.

-   **BOPPO**. Available from http://www.cprover.org/boppo/. BOPPO is
    a model checker that uses SAT-solving algorithms. BOPPO relies on a
    built-in SAT solver and Quantor, a solver for quantified boolean
    formulas that is currently bundled with BOPPO, but also available
    separately from <http://fmv.jku.at/quantor/>. We recommend to add
    the directories containing both tools to your `PATH` environment
    variable. Use the option

        --modelchecker boppo

    when you call SATABS and want it to use BOPPO instead of SMV.

-   **BOOM**. Available from http://www.cprover.org/boom/. Boom has a
    number of unique features, including the verification of programs
    with unbounded thread creation.

### Installing SATABS

1.  Download SATABS for your operating system. The binaries are
    available from <http://www.cprover.org/satabs/>.
2.  Unzip/untar the archive into a directory of your choice. We
    recommend to add this directory to your `PATH` environment variable.

Now you can execute SATABS. Try running SATABS on the small examples
presented in the \ref man_satabs-tutorials "SATABS tutorial". If you use
the Cadence SMV model checker, the only command line arguments you have
to specify are the names of the files that contain your program.


\subsection man_install-eclipse Installing the Eclipse Plugin

### Requirements

We provide a graphical user interface to CBMC and SATABS, which is
realized as a plugin to the Eclipse framework. Eclipse is available at
http://www.eclipse.org. We do not provide installation instructions for
Eclipse (basically, you only have to download the current version and
extract the files to your hard-disk) and assume that you have already
installed the current version.

CBMC and SATABS have their own requirements. As an example, both CBMC and SATABS require a suitable preprocessor and a set of header files. As
first step, you should therefore follow the installation instructions
for \ref man_install-cbmc "CBMC" and \ref man_install-satabs "SATABS".

Important note for Windows users: Visual Studio's `cl.exe` relies on a
complex set of environment variables to identify the target architecture
and the directories that contain the header files. You must run Eclipse
from within the *Visual Studio Command Prompt*.

### Installing the Eclipse Plugin

The installation instructions for the Eclipse Plugin, including the link
to the download site, are available
[here](http://www.cprover.org/eclipse-plugin/). This includes a small
tutorial on how to use the Eclipse plugin.


\section man_cbmc CBMC: Bounded Model Checking for C, C++ and Java

\subsection man_cbmc-tutorial A Short Tutorial

### First Steps

We assume you have already installed CBMC and the necessary support
files on your system. If not so, please follow the instructions
\ref man_install-cbmc "here".

Like a compiler, CBMC takes the names of .c files as command line
arguments. CBMC then translates the program and merges the function
definitions from the various .c files, just like a linker. But instead
of producing a binary for execution, CBMC performs symbolic simulation
on the program.

As an example, consider the following simple program, named file1.c:

    int puts(const char *s) { }

    int main(int argc, char **argv) {
      puts(argv[2]);
    }

Of course, this program is faulty, as the `argv` array might have fewer
than three elements, and then the array access `argv[2]` is out of
bounds. Now, run CBMC as follows:

    cbmc file1.c --show-properties --bounds-check --pointer-check

The two options `--bounds-check` and `--pointer-check` instruct CBMC to
look for errors related to pointers and array bounds. CBMC will print
the list of properties it checks. Note that it lists, among others, a
property labelled with "object bounds in argv" together with the location
of the faulty array access. As you can see, CBMC largely determines the
property it needs to check itself. This is realized by means of a
preliminary static analysis, which relies on computing a fixed point on
various [abstract
domains](http://en.wikipedia.org/wiki/Abstract_interpretation). More
detail on automatically generated properties is provided
\ref man_instrumentation-properties "here".

Note that these automatically generated properties need not necessarily
correspond to bugs – these are just *potential* flaws, as abstract
interpretation might be imprecise. Whether these properties hold or
correspond to actual bugs needs to be determined by further analysis.

CBMC performs this analysis using *symbolic simulation*, which
corresponds to a translation of the program into a formula. The formula
is then combined with the property. Let's look at the formula that is
generated by CBMC's symbolic simulation:

    cbmc file1.c --show-vcc --bounds-check --pointer-check

With this option, CBMC performs the symbolic simulation and prints the
verification conditions on the screen. A verification condition needs to
be proven to be valid by a [decision
procedure](http://en.wikipedia.org/wiki/Decision_problem) in order to
assert that the corresponding property holds. Let's run the decision
procedure:

    cbmc file1.c --bounds-check --pointer-check

CBMC transforms the equation you have seen before into CNF and passes it
to a SAT solver (more background on this step is in the book on
[Decision Procedures](http://www.decision-procedures.org/)). It then
determines which of the properties that it has generated for the program
hold and which do not. Using the SAT solver, CBMC detects that the
property for the object bounds of `argv` does not hold, and will thus
print a line as follows:

    [main.pointer_dereference.6] dereference failure: object bounds in argv[(signed long int)2]: FAILURE

### Counterexample Traces

Let us have a closer look at this property and why it fails. To aid the
understanding of the problem, CBMC can generate a *counterexample trace*
for failed properties. To obtain this trace, run

    cbmc file1.c --bounds-check --trace

CBMC then prints a counterexample trace, i.e., a program trace that
begins with `main` and ends in a state which violates the property. In
our example, the program trace ends in the faulty array access. It also
gives the values the input variables must have for the bug to occur. In
this example, `argc` must be one to trigger the out-of-bounds array
access. If you add a branch to the example that requires that `argc>=3`,
the bug is fixed and CBMC will report that the proofs of all properties
have been successful.

### Verifying Modules

In the example above, we used a program that starts with a `main`
function. However, CBMC is aimed at embedded software, and these kinds
of programs usually have different entry points. Furthermore, CBMC is
also useful for verifying program modules. Consider the following
example, called file2.c:

    int array[10];
    int sum() {
      unsigned i, sum;

      sum=0;
      for(i=0; i<10; i++)
        sum+=array[i];
    }

In order to set the entry point to the `sum` function, run

    cbmc file2.c --function sum --bounds-check

It is often necessary to build a suitable *harness* for the function in
order to set up the environment appropriately.

### Loop Unwinding

When running the previous example, you will have noted that CBMC unwinds
the `for` loop in the program. As CBMC performs Bounded Model Checking,
all loops have to have a finite upper run-time bound in order to
guarantee that all bugs are found. CBMC can optionally check that enough
unwinding is performed. As an example, consider the program binsearch.c:

    int binsearch(int x) {
      int a[16];
      signed low=0, high=16;

      while(low<high) {
        signed middle=low+((high-low)>>1);

        if(a[middle]<x)
          high=middle;
        else if(a[middle]>x)
          low=middle+1;
        else // a[middle]==x
          return middle;
      }

      return -1;
    }

If you run CBMC on this function, you will notice that the unwinding
does not stop on its own. The built-in simplifier is not able to
determine a run time bound for this loop. The unwinding bound has to be
given as a command line argument:

    cbmc binsearch.c --function binsearch --unwind 6 --bounds-check --unwinding-assertions

CBMC verifies that verifies the array accesses are within the bounds;
note that this actually depends on the result of the right shift. In
addition, as CBMC is given the option `--unwinding-assertions`, it also
checks that enough unwinding is done, i.e., it proves a run-time bound.
For any lower unwinding bound, there are traces that require more loop
iterations. Thus, CBMC will report that the unwinding assertion has
failed. As usual, a counterexample trace that documents this can be
obtained with the option `--property`.

### Unbounded Loops

CBMC can also be used for programs with unbounded loops. In this case,
CBMC is used for bug hunting only; CBMC does not attempt to find all
bugs. The following program (lock-example.c) is an example of a program
with a user-specified property:

    _Bool nondet_bool();
    _Bool LOCK = 0;

    _Bool lock() {
      if(nondet_bool()) {
        assert(!LOCK);
        LOCK=1;
        return 1; }

      return 0;
    }

    void unlock() {
      assert(LOCK);
      LOCK=0;
    }

    int main() {
      unsigned got_lock = 0;
      int times;

      while(times > 0) {
        if(lock()) {
          got_lock++;
          /* critical section */
        }

        if(got_lock!=0)
          unlock();

        got_lock--;
        times--;
      }
    }

The `while` loop in the `main` function has no (useful) run-time bound.
Thus, a bound has to be set on the amount of unwinding that CBMC
performs. There are two ways to do so:

1.  The `--unwind` command-line parameter can to be used to limit the
    number of times loops are unwound.
2.  The `--depth` command-line parameter can be used to limit the number
    of program steps to be processed.

Given the option `--unwinding-assertions`, CBMC checks whether the
arugment to `--unwind` is large enough to cover all program paths. If
the argument is too small, CBMC will detect that not enough unwinding is
done reports that an unwinding assertion has failed.

Reconsider the example. For a loop unwinding bound of one, no bug is
found. But already for a bound of two, CBMC detects a trace that
violates an assertion. Without unwinding assertions, or when using the
`--depth` command line switch, CBMC does not prove the program correct,
but it can be helpful to find program bugs. The various command line
options that CBMC offers for loop unwinding are described in the section
on \ref man_cbmc-loops "understanding loop unwinding".

### A Note About Compilers and the ANSI-C Library

Most C programs make use of functions provided by a library; instances
are functions from the standard ANSI-C library such as `malloc` or
`printf`. The verification of programs that use such functions has two
requirements:

1.  Appropriate header files have to be provided. These header files
    contain *declarations* of the functions that are to be used.
2.  Appropriate *definitions* have to be provided.

Most C compilers come with header files for the ANSI-C library
functions. We briefly discuss how to obtain/install these library files.

#### Linux

Linux systems that are able to compile software are usually equipped
with the appropriate header files. Consult the documentation of your
distribution on how to install the compiler and the header files. First
try to compile some significant program before attempting to verify it.

#### Windows

On Microsoft Windows, CBMC is pre-configured to use the compiler that is
part of Microsoft's Visual Studio. Microsoft's [Visual Studio
Community](http://www.visualstudio.com/en-us/products/visual-studio-community-vs)
is fully featured and available for download for free from the Microsoft
webpage. Visual Studio installs the usual set of header files together
with the compiler. However, the Visual Studio compiler requires a large
set of environment variables to function correctly. It is therefore
required to run CBMC from the *Visual Studio Command Prompt*, which can
be found in the menu *Visual Studio Tools*.

Note that in both cases, only header files are available. CBMC only
comes with a small set of definitions, which includes functions such as
`malloc`. Detailed information about the built-in definitions is
\ref man_instrumentation-libraries "here".

### Command Line Interface

This section describes the command line interface of CBMC. Like a C
compiler, CBMC takes the names of the .c source files as arguments.
Additional options allow to customize the behavior of CBMC. Use
`cbmc --help` to get a full list of the available options.

Structured output can be obtained from CBMC using the option `--xml-ui`.
Any output from CBMC (e.g., counterexamples) will then use an XML
representation.

### Further Reading

-   \ref man_cbmc-loops "Understanding Loop Unwinding"
-   [Hardware Verification using ANSI-C Programs as a
    Reference](http://www-2.cs.cmu.edu/~svc/papers/view-publications-ck03.html)
-   [Behavioral Consistency of C and Verilog Programs Using Bounded
    Model Checking](http://www-2.cs.cmu.edu/~svc/papers/view-publications-cky03.html)
-   [A Tool for Checking ANSI-C
    Programs](http://www-2.cs.cmu.edu/~svc/papers/view-publications-ckl2004.html)

We also have a [list of interesting applications of
CBMC](http://www.cprover.org/cbmc/applications/).


\subsection man_cbmc-loops Understanding Loop Unwinding

### Iteration-based Unwinding

The basic idea of CBMC is to model the computation of the programs up to
a particular depth. Technically, this is achieved by a process that
essentially amounts to *unwinding loops*. This concept is best
illustrated with a generic example:

    int main(int argc, char **argv) {
      while(cond) {
        BODY CODE
      }
    }

A BMC instance that will find bugs with up to five iterations of the
loop would contain five copies of the loop body, and essentially
corresponds to checking the following loop-free program:

    int main(int argc, char **argv) {
      if(cond) {
        BODY CODE COPY 1
        if(cond) {
          BODY CODE COPY 2
          if(cond) {
            BODY CODE COPY 3
            if(cond) {
              BODY CODE COPY 4
              if(cond) {
                BODY CODE COPY 5
              }
            }
          }
        }
      }
    }

Note the use of the `if` statement to prevent the execution of the loop
body in the case that the loop ends before five iterations are executed.
The construction above is meant to produce a program that is trace
equivalent with the original programs for those traces that contain up
to five iterations of the loop.

In many cases, CBMC is able to automatically determine an upper bound on
the number of loop iterations. This may even work when the number of
loop unwindings is not constant. Consider the following example:

    _Bool f();

    int main() {
      for(int i=0; i<100; i++) {
        if(f()) break;
      }
      assert(0);
    }

The loop in the program above has an obvious upper bound on the number
of iterations, but note that the loop may abort prematurely depending on
the value that is returned by `f()`. CBMC is nevertheless able to
automatically unwind the loop to completion.

This automatic detection of the unwinding bound may fail if the number
of loop iterations is highly data-dependent. Furthermore, the number of
iterations that are executed by any given loop may be too large or may
simply be unbounded. For this case, CBMC offers the command-line option
`--unwind B`, where `B` denotes a number that corresponds to the maximal
number of loop unwindings CBMC performs on any loop.

Note that the number of unwindings is measured by counting the number of
*backjumps*. In the example above, note that the condition `i<100` is in
fact evaluated 101 times before the loop terminates. Thus, the loop
requires a limit of 101, and not 100.

### Setting Separate Unwinding Limits

The setting given with `--unwind` is used globally, that is, for all
loops in the program. In order to set individual limits for the loops,
first use

    --show-loops

to obtain a list of all loops in the program. Then identify the loops
you need to set a separate bound for, and note their loop ID. Then use

    --unwindset L:B,L:B,...

where `L` denotes a loop ID and `B` denotes the bound for that loop.

As an example, consider a program with two loops in the function main:

    --unwindset c::main.0:10,c::main.1:20

This sets a bound of 10 for the first loop, and a bound of 20 for the
second loop.

What if the number of unwindings specified is too small? In this case,
bugs that require paths that are deeper may be missed. In order to
address this problem, CBMC can optionally insert checks that the given
unwinding bound is actually sufficiently large. These checks are called
*unwinding assertions*, and are enabled with the option
`--unwinding-assertions`. Continuing the generic example above, this
unwinding assertion for a bound of five corresponds to checking the
following loop-free program:

    int main(int argc, char **argv) {
      if(cond) {
        BODY CODE COPY 1
        if(cond) {
          BODY CODE COPY 2
          if(cond) {
            BODY CODE COPY 3
            if(cond) {
              BODY CODE COPY 4
              if(cond) {
                BODY CODE COPY 5
                assert(!cond);
              }
            }
          }
        }
      }
    }

The unwinding assertions can be verified just like any other generated
assertion. If all of them are proven to hold, the given loop bounds are
sufficient for the program. This establishes a [high-level worst-case
execution time](http://en.wikipedia.org/wiki/Worst-case_execution_time)
(WCET).

In some cases, it is desirable to cut off very deep loops in favor of
code that follows the loop. As an example, consider the following
program:

    int main() {
      for(int i=0; i<10000; i++) {
        BODY CODE
      }
      assert(0);
    }

In the example above, small values of `--unwind` will prevent that the
assertion is reached. If the code in the loop is considered irrelevant
to the later assertion, use the option

    --partial-loops

This option will allow paths that execute loops only partially, enabling
a counterexample for the assertion above even for small unwinding
bounds. The disadvantage of using this option is that the resulting path
may be spurious, i.e., may not exist in the original program.

### Depth-based Unwinding

The loop-based unwinding bound is not always appropriate. In particular,
it is often difficult to control the size of the generated formula when
using the `--unwind` option. The option

    --depth nr

specifies an unwinding bound in terms of the number of instructions that
are executed on a given path, irrespectively of the number of loop
iterations. Note that CBMC uses the number of instructions in the
control-flow graph as the criterion, not the number of instructions in
the source code.

\subsection man_cbmc-cover COVER: Test Suite Generation with CBMC


### A Small Tutorial with A Case Study

We assume that CBMC is installed on your system. If not so, follow
\ref man_install-cbmc "these instructions".

CBMC can be used to automatically generate test cases that satisfy a
certain [code coverage](https://en.wikipedia.org/wiki/Code_coverage)
criteria. Common coverage criteria include branch coverage, condition
coverage and [Modified Condition/Decision Coverage
(MC/DC)](https://en.wikipedia.org/wiki/Modified_condition/decision_coverage).
Among others, MC/DC is required by several avionics software development
guidelines to ensure adequate testing of safety critical software.
Briefly, in order to satisfy MC/DC, for every conditional statement
containing boolean decisions, each Boolean variable should be evaluated
one time to "true" and one time to "false", in a way that affects the
outcome of the decision.

In the following, we are going to demonstrate how to apply the test
suite generation functionality in CBMC, by means of a case study. The
following program is an excerpt from a real-time embedded benchmark
[PapaBench](https://www.irit.fr/recherches/ARCHI/MARCH/rubrique.php3?id_rubrique=97),
and implements part of a fly-by-wire autopilot for an Unmanned Aerial
Vehicle (UAV). It is adjusted mildly for our purposes.

The aim of function `climb_pid_run` is to control the vertical climb of
the UAV. Details on the theory behind this operation are documented in
the [wiki](https://wiki.paparazziuav.org/wiki/Theory_of_Operation) for
the Paparazzi UAV project. The behaviour of this simple controller,
supposing that the desired speed is 0.5 meters per second, is plotted in
the Figure below.

\image html pid.png "The pid controller"

    01: // CONSTANTS:
    02: #define MAX_CLIMB_SUM_ERR 10
    03: #define MAX_CLIMB 1
    04:
    05: #define CLOCK 16
    06: #define MAX_PPRZ (CLOCK*600)
    07:
    08: #define CLIMB_LEVEL_GAZ 0.31
    09: #define CLIMB_GAZ_OF_CLIMB 0.75
    10: #define CLIMB_PITCH_OF_VZ_PGAIN 0.05
    11: #define CLIMB_PGAIN -0.03
    12: #define CLIMB_IGAIN 0.1
    13:
    14: const float pitch_of_vz_pgain=CLIMB_PITCH_OF_VZ_PGAIN;
    15: const float climb_pgain=CLIMB_PGAIN;
    16: const float climb_igain=CLIMB_IGAIN;
    17: const float nav_pitch=0;
    18:
    19: /** PID function INPUTS */
    20: // The user input: target speed in vertical direction
    21: float desired_climb;
    22: // Vertical speed of the UAV detected by GPS sensor
    23: float estimator_z_dot;
    24:
    25: /** PID function OUTPUTS */
    26: float desired_gaz;
    27: float desired_pitch;
    28:
    29: /** The state variable: accumulated error in the control */
    30: float climb_sum_err=0;
    31:
    32: /** Computes desired_gaz and desired_pitch */
    33: void climb_pid_run()
    34: {
    35:
    36:   float err=estimator_z_dot-desired_climb;
    37:
    38:   float fgaz=climb_pgain*(err+climb_igain*climb_sum_err)+CLIMB_LEVEL_GAZ+CLIMB_GAZ_OF_CLIMB*desired_climb;
    39:
    40:   float pprz=fgaz*MAX_PPRZ;
    41:   desired_gaz=((pprz>=0 && pprz<=MAX_PPRZ) ? pprz : (pprz>MAX_PPRZ ? MAX_PPRZ : 0));
    42:
    43:   /** pitch offset for climb */
    44:   float pitch_of_vz=(desired_climb>0) ? desired_climb*pitch_of_vz_pgain : 0;
    45:   desired_pitch=nav_pitch+pitch_of_vz;
    46:
    47:   climb_sum_err=err+climb_sum_err;
    48:   if (climb_sum_err>MAX_CLIMB_SUM_ERR) climb_sum_err=MAX_CLIMB_SUM_ERR;
    49:   if (climb_sum_err<-MAX_CLIMB_SUM_ERR) climb_sum_err=-MAX_CLIMB_SUM_ERR;
    50:
    51: }
    52:
    53: int main()
    54: {
    55:
    56:   while(1)
    57:   {
    58:     /** Non-deterministic input values */
    59:     desired_climb=nondet_float();
    60:     estimator_z_dot=nondet_float();
    61:
    62:     /** Range of input values */
    63:     __CPROVER_assume(desired_climb>=-MAX_CLIMB && desired_climb<=MAX_CLIMB);
    64:     __CPROVER_assume(estimator_z_dot>=-MAX_CLIMB && estimator_z_dot<=MAX_CLIMB);
    65:
    66:     __CPROVER_input("desired_climb", desired_climb);
    67:     __CPROVER_input("estimator_z_dot", estimator_z_dot);
    68:
    69:     climb_pid_run();
    70:
    71:     __CPROVER_output("desired_gaz", desired_gaz);
    72:     __CPROVER_output("desired_pitch", desired_pitch);
    73:
    74:   }
    75:
    76:   return 0;
    77: }

In order to test the PID controller, we construct a main control loop,
which repeatedly invokes the function `climb_pid_run` (line 69). This
PID function has two input variables: the desired speed `desired_climb`
and the estimated speed `estimated_z_dot`. In the beginning of each loop
iteration, values of the inputs are assigned non-deterministically.
Subsequently, the `__CPROVER_assume` statement in lines 63 and 64
guarantees that both values are bounded within a valid range. The
`__CPROVER_input` and `__CPROVER_output` will help clarify the inputs
and outputs of interest for generating test suites.

To demonstrate the automatic test suite generation in CBMC, we call the
following command and we are going to explain the command line options
one by one.

    cbmc pid.c --cover mcdc --unwind 6 --xml-ui

The option `--cover mcdc` specifies the code coverage criterion. There
are four conditional statements in the PID function: in line 41, line
44, line 48 and line 49. To satisfy MC/DC, the test suite has to meet
multiple requirements. For instance, each conditional statement needs to
evaluate to *true* and *false*. Consider the condition
`"pprz>=0 && pprz<=MAX_PPRZ"` in line 41. CBMC instruments three
coverage goals to control the respective evaluated results of
`"pprz>=0"` and `"pprz<=MAX_PPRZ"`. We list them in below and they
satisfy the MC/DC rules. Note that `MAX_PPRZ` is defined as 16 \* 600 in
line 06 of the program.

    !(pprz >= (float)0) && pprz <= (float)(16 * 600)  id="climb_pid_run.coverage.1"
    pprz >= (float)0 && !(pprz <= (float)(16 * 600))  id="climb_pid_run.coverage.2"
    pprz >= (float)0 && pprz <= (float)(16 * 600)     id="climb_pid_run.coverage.3"

The "id" of each coverage goal is automatically assigned by CBMC. For
every coverage goal, a test suite (if there exists) that satisfies such
a goal is printed out in XML format, as the parameter `--xml-ui` is
given. Multiple coverage goals can share a test suite, when the
corresponding execution of the program satisfies all these goals at the
same time.

In the end, the following test suites are automatically generated for
testing the PID controller. A test suite consists of a sequence of input
parameters that are passed to the PID function `climb_pid_run` at each
loop iteration. For example, Test 1 covers the MC/DC goal with
id="climb\_pid\_run.coverage.1". The complete output from CBMC is in
[pid\_test\_suites.xml](pid_test_suites.xml), where every test suite and
the coverage goals it is for are clearly described.

    Test suite:
    Test 1.
      (iteration 1) desired_climb=-1.000000f, estimator_z_dot=1.000000f

    Test 2.
      (iteration 1) desired_climb=-1.000000f, estimator_z_dot=1.000000f
      (iteration 2) desired_climb=1.000000f, estimator_z_dot=-1.000000f

    Test 3.
      (iteration 1) desired_climb=0.000000f, estimator_z_dot=-1.000000f
      (iteration 2) desired_climb=1.000000f, estimator_z_dot=-1.000000f

    Test 4.
      (iteration 1) desired_climb=1.000000f, estimator_z_dot=-1.000000f
      (iteration 2) desired_climb=1.000000f, estimator_z_dot=-1.000000f
      (iteration 3) desired_climb=1.000000f, estimator_z_dot=-1.000000f
      (iteration 4) desired_climb=1.000000f, estimator_z_dot=-1.000000f
      (iteration 5) desired_climb=0.000000f, estimator_z_dot=-1.000000f
      (iteration 6) desired_climb=1.000000f, estimator_z_dot=-1.000000f

    Test 5.
      (iteration 1) desired_climb=-1.000000f, estimator_z_dot=1.000000f
      (iteration 2) desired_climb=-1.000000f, estimator_z_dot=1.000000f
      (iteration 3) desired_climb=-1.000000f, estimator_z_dot=1.000000f
      (iteration 4) desired_climb=-1.000000f, estimator_z_dot=1.000000f
      (iteration 5) desired_climb=-1.000000f, estimator_z_dot=1.000000f
      (iteration 6) desired_climb=-1.000000f, estimator_z_dot=1.000000f

The option `--unwind 6` unwinds the loop inside the main function body
six times. In order to achieve the complete coverage on all the
instrumented goals in the PID function `climb_pid_run`, the loop must be
unwound sufficient enough times. For example, `climb_pid_run` needs to
be called at least six times for evaluating the condition
`climb_sum_err>MAX_CLIMB_SUM_ERR` in line 48 to *true*. This corresponds
to the Test 5. An introduction to the use of loop unwinding can be found
in [Understanding Loop Unwinding](cbmc-loops.shtml).

In this small tutorial, we present the automatic test suite generation
functionality of CBMC, by applying the MC/DC code coverage criterion to
a PID controller case study. In addition to `--cover mcdc`, other
coverage criteria like `branch`, `decision`, `path` etc. are also
available when calling CBMC.

### Coverage Criteria

The table below summarizes the coverage criteria that CBMC supports.

Criterion |Definition
----------|----------
assertion |For every assertion, generate a test that reaches it
location  |For every location, generate a test that reaches it
branch    |Generate a test for every branch outcome
decision  |Generate a test for both outcomes of every Boolean expression that is not an operand of a propositional connective
condition |Generate a test for both outcomes of every Boolean expression
mcdc      |Modified Condition/Decision Coverage (MC/DC)
path      |Bounded path coverage
cover     |Generate a test for every `__CPROVER_cover` statement


\section man_satabs SATABS---Predicate Abstraction with SAT

\subsection man_satabs-overview Overview

This section describes SATABS from the point of view of the user. To
learn about the technology implemented in SATABS, read
\ref man_satabs-background "this".

We assume you have already installed SATABS and the necessary support
files on your system. If not so, please follow
\ref man_install-satabs "these instructions".

While users of SATABS almost never have to be concerned about the
underlying refinement abstraction algorithms, understanding the classes
of properties that can be verified is crucial. Predicate abstraction is
most effective when applied to *control-flow dominated properties*. As
an example, reconsider the following program (lock-example-fixed.c):

    _Bool nondet_bool();
    _Bool LOCK = 0;

    _Bool lock() {
      if(nondet_bool()) {
        assert(!LOCK);
        LOCK=1;
        return 1; }

      return 0;
    }

    void unlock() {
      assert(LOCK);
      LOCK=0;
    }

    int main() {
      unsigned got_lock = 0;
      int times;

      while(times > 0) {
        if(lock()) {
          got_lock++;
          /* critical section */
        }

        if(got_lock!=0) {
          unlock();
          got_lock--;
        }

        times--;
      }
    }

The two assertions in the program model that the functions `lock()` and
`unlock()` are called in the right order. Note that the value of `times`
is chosen non-deterministically and is not bounded. The program has no
run-time bound, and thus, unwinding the code with CBMC will never
terminate.

### Working with Claims

The two assertions will give rise to two *properties*. Each property is
associated to a specific line of code, i.e., a property is violated when
some condition can become false at the corresponding program location.
SATABS will generate a list of all properties for the programs as
follows:

    satabs lock-example-fixed.c --show-properties

SATABS will list two properties; each property corresponds to one of the
two assertions. We can use SATABS to verify both properties as follows:

    satabs lock-example-fixed.c

SATABS will conclude the verification successfully, that is, both
assertions hold for execution traces of any length.

By default, SATABS attempts to verify all properties at once. A single
property can be verified (or refuted) by using the `--property id`
option of SATABS, where `id` denotes the identifier of the property in
the list obtained by calling SATABS with the `--show-properties` flag.
Whenever a property is violated, SATABS reports a feasible path that
leads to a state in which the condition that corresponds to the violated
property evaluates to false.

\subsection man_satabs-libraries Programs that use Libraries

SATABS cannot check programs that use functions that are only available
in binary (compiled) form (this restriction is not imposed by the
verification algorithms that are used by SATABS – they also work on
assembly code). The reason is simply that so far no assembly language
frontend is available for SATABS. At the moment, (library) functions for
which no C source code is available have to be replaced by stubs. The
usage of stubs and harnesses (as known from unit testing) also allows to
check more complicated properties (like, for example, whether function
`fopen` is always called before `fclose`). This technique is explained
in detail in the \ref man_satabs-tutorials "SATABS tutorials".

\subsection man_satabs-unit-test Unit Testing with SATABS

The example presented \ref man_satabs-tutorial-driver "here" is
obviously a toy example and can hardly be used to convince your project
manager to use static verification in your next project. Even though we
recommend to use formal verification and specification already in the
early phases of your project, the sad truth is that in most projects
verification (of any kind) is still pushed to the very end of the
development cycle.  Therefore, this section is dedicated to the
verification of legacy code.  However, the techniques presented here can
also be used for *unit testing*.

Unit testing is used in most software development projects, and static
verification with SATABS can be very well combined with this technique.
Unit testing relies on a number test cases that yield the desired code
coverage. Such test cases are implemented by a software testing engineer
in terms of a test harness (aka test driver) and a set of function
stubs. Typically, a slight modification to the test harness allows it to
be used with SATABS. Replacing the explicit input values with
non-deterministic inputs (as explained in
\ref man_satabs-tutorial-aeon "here" and
\ref man_satabs-tutorial-driver "here")) guarantees that SATABS will try
to achieve **full** path and state coverage (due to the fact that
predicate abstraction implicitly detects equivalence classes). However,
it is not guaranteed that SATABS terminates in all cases. Keep in mind
that you must not make any assumptions about the validity of the
properties if SATABS did not run to completion!

### Further Reading

-   [Model Checking Concurrent Linux Device
    Drivers](http://www.kroening.com/publications/view-publications-wbwk2007.html)
-   [SATABS: SAT-based Predicate Abstraction for
    ANSI-C](http://www-2.cs.cmu.edu/~svc/papers/view-publications-cksy2005.html)
-   [Predicate Abstraction of ANSI-C Programs using
    SAT](http://www-2.cs.cmu.edu/~svc/papers/view-publications-cksy2004.html)

\subsection man_satabs-background Background

### Sound Abstractions

This section provides background information on how SATABS operates.
Even for very trivial C programs it is impossible to exhaustively
examine their state space (which is potentially unbounded). However, not
all details in a C program necessarily contribute to a bug, so it may be
sufficient to only examine those parts of the program that are somehow
related to a bug.

In practice, many static verification tools (such as `lint`) try to
achieve this goal by applying heuristics. This approach comes at a cost:
bugs might be overlooked because the heuristics do not cover all
relevant aspects of the program. Therefore, the conclusion that a
program is correct whenever such a static verification tool is unable to
find an error is invalid.

\image html cegar-1.png "CEGAR Loop"

A more sophisticated approach that has been very successful recently is
to generate a *sound* abstraction of the original program. In this
context, *soundness* refers to the fact that the abstract program
contains (at least) all relevant behaviors (i.e., bugs) that are present
in the original program. In the Figure above, the first component strips
details from the original program. The number of possible behaviors
increases as the number of details in the abstract program decreases.
Intuitively, the reason is that whenever the model checking tool lacks
the information that is necessary to make an accurate decision on
whether a branch of an control flow statement can be taken or not, both
branches have to be considered.

In the resulting *abstract program*, a set of concrete states is
subsumed by means of a single abstract state. Consider the following
figure:

![](states.png)

The concrete states *x*~1~ and *x*~2~ are mapped to an abstract state
*X*, and similarly *Y* subsumes *y*~1~ and *y*~2~. However, all
transitions that are possible in the concrete program are also possible
in the abstract model. The abstract transition *X* → *Y* summarizes the
concrete transitions *x*~1~ → *y*~1~ and *x*~1~ → *x*~1~, and *Y* → *X*
corresponds to *x*~1~ → *x*~2~. The behavior *X* → *Y* → *X* is feasible
in the original program, because it maps to *x*~1~ → *x*~1~ → *x*~2~.
However, *Y* → *X* → *Y* is feasible only in the abstract model.

### Spurious Counterexamples

The consequence is that the model checker (component number two in the
figure above) possibly reports a *spurious* counterexample. We call a
counterexample spurious whenever it is feasible in the current abstract
model but not in the original program. However, whenever the model
checker is unable to find an execution trace that violates the given
property, we can conclude that there is no such trace in the original
program, either.

The feasibility of counterexamples is checked by *symbolic simulation*
(performed by component three in the figure above). If the
counterexample is indeed feasible, SATABS found a bug in the original
program and reports it to the user.

### Automatic Refinement

On the other hand, infeasible counterexamples (that originate from
abstract behaviors that result from the omission of details and are not
present in the original program) are never reported to the user.
Instead, the information is used in order to refine the abstraction such
that the spurious counterexample is not part of the refined model
anymore. For instance, the reason for the infeasibility of *Y* → *X* →
*Y* is that neither *y*~1~ nor *x*~1~ can be reached from *x*~2~.
Therefore, the abstraction can be refined by partitioning *X*.

The refinement steps can be illustrated as follows:

![Iterative refinement](refinement.png)

The first step (1) is to generate a very coarse abstraction with a very
small state space. This abstraction is then successively refined (2, 3,
...) until either a feasible counterexample is found or the abstract
program is detailed enough to show that there is no path that leads to a
violation of the given property. The problem is that this point is not
necessarily reached for every input program, i.e., it is possible that
the the abstraction refinement loop never terminates. Therefore, SATABS
allows to specify an upper bound for the number of iterations.

When this upper bound is reached and no counterexample was found, this
does not necessarily mean that there is none. In this case, you cannot
make any conclusions at all with respect to the correctness of the input
program.

\subsection man_satabs-tutorials Tutorials

We provide an introduction to model checking "real" C programs with
SATABS using two small examples.

\subsubsection man_satabs-tutorial-driver Reference Counting in Linux Device Drivers

Microsoft's [SLAM](http://research.microsoft.com/SLAM) toolkit has been
successfully used to find bugs in Windows device drivers. SLAM
automatically verifies device driver whether a device driver adheres to
a set of specifications. SLAM provides a test harness for device drivers
that calls the device driver dispatch routines in a non-deterministic
order. Therefore, the Model Checker examines all combinations of calls.
Motivated by the success this approach, we provide a toy example based
on Linux device drivers. For a more complete approach to the
verification of Linux device drivers, consider
[DDVerify](http://www.cprover.org/ddverify/).

Dynamically loadable modules enable the Linux Kernel to load device
drivers on demand and to release them when they are not needed anymore.
When a device driver is registered, the kernel provides a major number
that is used to uniquely identify the device driver. The corresponding
device can be accessed through special files in the filesystem; by
convention, they are located in the `/dev` directory. If a process
accesses a device file the kernel calls the corresponding `open`, `read`
and `write` functions of the device driver. Since a driver must not be
released by the kernel as long as it is used by at least one process,
the device driver must maintain a usage counter (in more recent Linux
kernels, this is done automatically, however, drivers that must maintain
backward compatibility have to adjust this counter).

We provide a skeleton of such a driver. Download the files
assets/spec.c, assets/driver.c, assets/driver.h, assets/kdev_t.h, and
assets/modules.h.

The driver contains following functions:

1.  `register_chrdev`: (in assets/spec.c) Registers a character device.
    In our implementation, the function sets the variable `usecount` to
    zero and returns a major number for this device (a constant, if the
    user provides 0 as argument for the major number, and the value
    specified by the user otherwise).

        int usecount;

        int register_chrdev (unsigned int major, const char* name)
        {
          usecount = 0;
          if (major == 0)
            return MAJOR_NUMBER;
          return major;
        }

2.  `unregister_chrdev`: (in assets/spec.c) Unregisters a character
    device.  This function asserts that the device is not used by any
    process anymore (we use the macro `MOD_IN_USE` to check this).

        int unregister_chrdev (unsigned int major, const char* name)
        {
          if (MOD_IN_USE)
            {
            ERROR: assert (0);
            }
          else
            return 0;
        }

3.  `dummy_open`: (in assets/driver.c) This function increases the
    `usecount`. If the device is locked by some other process
    `dummy_open` returns -1. Otherwise it locks the device for the
    caller.

4.  `dummy_read`: (in assets/driver.c) This function "simulates" a read
    access to the device. In fact it does nothing, since we are
    currently not interested in the potential buffer overflow that may
    result from a call to this function. Note the usage of the function
    `nondet_int`: This is an internal SATABS-function that
    non­determi­nistically returns an arbitrary integer value. The
    function `__CPROVER_assume` tells SATABS to ignore all traces that
    do not adhere to the given assumption. Therefore, whenever the lock
    is held, `dummy_read` will return a value between 0 and `max`. If
    the lock is not held, then `dummy_read` returns -1.

5.  `dummy_release`: (in assets/driver.c) If the lock is held, then
    `dummy_release` decreases the `usecount`, releases the lock, and
    returns 0. Otherwise, the function returns -1.

We now want to check if any *valid* sequence of calls of the dispatch
functions (in driver.c) can lead to the violation of the assertion (in
assets/spec.c). Obviously, a call to `dummy_open` that is immediately
followed by a call to `unregister_chrdev` violates the assertion.

The function `main` in spec.c gives an example of how these functions
are called. First, a character device "`dummy`" is registered. The major
number is stored in the `inode` structure of the device. The values for
the file structure are assigned non-deterministically. We rule out
invalid sequences of calls by ensuring that no device is unregistered
while it is still locked. We use the following model checking harness
for calling the dispatching functions:

    random = nondet_uchar ();
    __CPROVER_assume (0 <= random && random <= 3);

    switch (random)
    {
    case 1:
      rval = dummy_open (&inode, &my_file);
      if (rval == 0)
        lock_held = TRUE;
      break;
    case 2:
      __CPROVER_assume (lock_held);
      count = dummy_read (&my_file, buffer, BUF_SIZE);
      break;
    case 3:
      dummy_release (&inode, &my_file);
      lock_held = FALSE;
      break;
    default:
      break;
    }

The variable `random` is assigned non-deterministically. Subsequently,
the value of `random` is restricted to be 0 &le `random` ≤ 3 by a call
to `__CPROVER_assume`. Whenever the value of `random` is not in this
interval, the corresponding execution trace is simply discarded by
SATABS. Depending on the value of `random`, the harness calls either
`dummy_open`, `dummy_read` or `dummy_close`. Therefore, if there is a
sequence of calls to these three functions that leads to a violation of
the assertion in `unregister_chrdev`, then SATABS will eventually
consider it.

If we ask SATABS to show us the properties it verifies with

    satabs driver.c spec.c --show-properties

for our example, we obtain

1.  Claim unregister\_chrdev.1:\
        file spec.c line 18 function unregister\_chrdev\
        MOD\_IN\_USE in unregister\_chrdev\
        FALSE

2.  Claim dummy\_open.1:\
        file driver.c line 15 function dummy\_open\
        i\_rdev mismatch\
        (unsigned int)inode-&gt;i\_rdev &gt;&gt; 8 == (unsigned
    int)dummy\_major

It seems obvious that the property dummy\_open.1 can never be violated.
SATABS confirms this assumption: We call

    satabs driver.c spec.c --property dummy_open.1

and SATABS reports `VERIFICATION SUCCESSFUL` after a few iterations.

If we try to verify property unregister\_chrdev.1, SATABS reports that
the property in line 18 in file spec.c is violated (i.e., the assertion
does not hold, therefore the `VERIFICATION FAILED`). Furthermore, SATABS
provides a detailed description of the problem in the form of a
counterexample (i.e., an execution trace that violates the property). On
this trace, `dummy_open` is called **twice**, leading to a `usecount` of 2.
The second call of course fails with `rval=-1`, but the counter is
increased nevertheless:

    int dummy_open (struct inode *inode, struct file *filp)
    {
      __CPROVER_assert(MAJOR (inode->i_rdev) == dummy_major,
          "i_rdev mismatch");
      MOD_INC_USE_COUNT;

      if (locked)
        return -1;
      locked = TRUE;

      return 0; /* success */
    }

Then, `dummy_release` is called to release the lock on the device.
Finally, the loop is left and the call to `unregister_chrdev` results in
a violation of the assertion (since `usecount` is still 1, even though
`locked=0`).

\subsubsection man_satabs-tutorial-aeon Buffer Overflow in a Mail Transfer Agent

We explain how to model check Aeon version 0.2a, a small mail transfer
agent written by Piotr Benetkiewicz. The description advertises Aeon as
a "*good choice for **hardened** or minimalistic boxes*". The sources
are available
[here](http://www.cprover.org/satabs/examples/loop_detection/aeon-0.2a.tar.gz).

Our first naive attempt to verify Aeon using

    satabs *.c

produces a positive result, but also warns us that the property holds
trivially. It also reveals that a large number library functions are
missing: SATABS is unable to find the source code for library functions
like `send`, `write` and `close`.

Now, do you have to provide a body for all missing library functions?
There is no easy answer to this question, but a viable answer would be
"most likely not". It is necessary to understand how SATABS handles
functions without bodies: It simply assumes that such a function returns
an arbitrary value, but that no other locations than the one on the left
hand side of the assignment are changed. Obviously, there are cases in
which this assumption is un­sound, since the function potentially
modifies all memory locations that it can somehow address.

We now use static analysis to generate array bounds checks for Aeon:

    satabs *.c --pointer-check --bounds-check --show-properties

SATABS will show about 300 properties in various functions (read
\ref man_instrumentation-properties "this" for more information on the
property instrumentation). Now consider the first few lines of the
`main` function of Aeon:

    int main(int argc, char **argv)
    {
      char settings[MAX_SETTINGS][MAX_LEN];
      ...
      numSet = getConfig(settings);
      if (numSet == -1) {
        logEntry("Missing config file!");
        exit(1);
      }
      ...

and the function `getConfig` in `lib_aeon.c`:

    int getConfig(char settings[MAX_SETTINGS][MAX_LEN])
    {
        char home[MAX_LEN];
    FILE *fp;	/* .rc file handler */
    int numSet = 0;	/* number of settings */

    strcpy(home, getenv("HOME"));  	/* get home path */
    strcat(home, "/.aeonrc");	/* full path to rc file */
    fp = fopen(home, "r");
    if (fp == NULL) return -1;	/* no cfg - ERROR */
      while (fgets(settings[numSet], MAX_LEN-1, fp)
        && (numSet < MAX_SETTINGS)) numSet++;
    fclose(fp);

    return numSet;
    }

The function `getConfig` makes calls to `strcpy`, `strcat`, `getenv`,
`fopen`, `fgets`, and `fclose`. It is very easy to provide an
implementation for the functions from the string library (string.h), and
SATABS comes with meaningful definitions for most of them. The
definition of `getenv` is not so straight-forward. The man-page of
`getenv` (which we obtain by entering `man 3 getenv` in a Unix or cygwin
command prompt) tells us:

    `` `getenv' `` searches the list of en­vi­ron­ment variable names
    and values (using the global pointer `char **environ`) for a
    variable whose name matches the string at `NAME`. If a variable name
    matches, `getenv` returns a pointer to the associated value.

SATABS has no information whatsoever about the content of `environ`.
Even if SATABS could access the environment variables on your
computer, a successful verification of `Aeon` would then only guarantee
that the properties for this program hold on your computer with a
specific set of en­vi­ron­ment variables. We have to assume that
`environ` contains en­vi­ron­ment variables that have an arbitrary
content of arbitrary length. The content of en­vi­ron­ment variables is
not only arbitrary but could be malefic, since it can be modified by the
user. The approximation of the behavior of `getenv` that is shipped with
SATABS completely ignores the content of the string.

Now let us have another look at the properties that SATABS generates for
the models of the the string library and for `getenv`. Most of these
properties require that we verify that the upper and lower bounds of
buffers or arrays are not violated. Let us look at one of the properties
that SATABS generates for the code in function `getConfig`:

    Claim getConfig.3:   file lib_aeon.c line 19 function getConfig   dereference failure: NULL plus offset pointer   !(SAME-OBJECT(src, NULL))`

The model of the function `strcpy` dereferences the pointer returned by
`getenv`, which may return a NULL pointer. This possibility is detected
by the static analysis, and thus a corresponding property is generated.
Let us check this specific property:

    satabs *.c --pointer-check --bounds-check --property getConfig.3

SATABS immediately returns a counterexample path that demonstrates how
`getenv` returns a NULL, which is subsequently dereferenced. We have
identified the first bug in this program: it requires that the
environment variable HOME is set, and crashes otherwise.

Let us examine one more property in the same function:

    Claim getConfig.7:   file lib_aeon.c line 19 function getConfig   dereference failure: array `home' upper bound   !(POINTER_OFFSET(dst) + (int)i >= 512) || !(SAME-OBJECT(dst, &home[0]))

This property asserts that the upper bound of the array `home` is not
violated. The variable `home` looks familiar: We encountered it in the
function `getConfig` given above. The function `getenv` in combination
with functions `strcpy`, `strcat` or `sprintf` is indeed often the
source for buffer overflows. Therefore, we try to use SATABS to check
the upper bound of the array `home`:

    satabs *.c --pointer-check --bounds-check --property getConfig.7

SATABS runs for quite a while and will eventually give up, telling us
that its upper bound for abstraction refinement iterations has been
exceeded. This is not exactly the result we were hoping for, and we
could now increase the bound for iterations with help of the
`--iterations` command line switch of SATABS.

Before we do this, let us investigate why SATABS has failed to provide a
useful result. The function `strcpy` contains a loop that counts from 1
to the length of the input string. Predicate abstraction, the mechanism
SATABS is based on, is unable to detect such loops and will therefore
unroll the loop body as often as necessary. The array `home` has
`MAX_LEN` elements, and `MAX_LEN` is defined to be 512 in `aeon.h`.
Therefore, SATABS would have to run through at least 512 iterations,
only to verify (or reject) one of the more than 300 properties! Does
this fact defeat the purpose of static verification?

We can make the job easier: after reducing the value of `MAX_LEN` in
`aeon.h` to a small value, say to 10, SATABS provides a counterexample
trace that demonstrates how the buffer overflow be reproduced. If you
use the Eclipse plugin (as described \ref man_install-eclipse "here"),
you can step through this counterexample. The trace contains the string
that is returned by `getenv`.


\section man_modelling Modelling

\subsection man_modelling-nondet Nondeterminism

### Rationale

Programs typically read inputs from an environment. These inputs can
take the form of data read from a file, keyboard or network socket, or
arguments passed on the command line. It is usually desirable to analyze
the program for any choice of these inputs. In Model Checking, inputs
are therefore modeled by means of *nondeterminism*, which means that the
value of the input is not specified. The program may follow any
computation that results from any choice of inputs.

### Sources of Nondeterminism

The CPROVER tools support the following sources of nondeterminism:

- functions that read inputs from the environments;
- the thread schedule in concurrent programs;
- initial values of local-scoped variables and memory allocated with
  `malloc`;
- initial values of variables that are `extern` in all compilation
  units;
- explicit functions for generating nondeterminism.

The CPROVER tools are shipped with a number of stubs for the most
commonly used library functions. When executing a statement such as
`getchar()`, a nondeterministic value is chosen instead of reading a
character from the keyboard.

When desired, nondeterminism can be introduced explicitly into the
program by means of functions that begin with the prefix `nondet_`. As
an example, the following function returns a nondeterministically chosen
unsigned short int:

    unsigned short int nondet_ushortint();

Note that the body of the function is not defined. The name of the
function itself is irrelevant (save for the prefix), but must be unique.
Also note that a nondeterministic choice is not to be confused with a
probabilistic (or random) choice.

### Uninterpreted Functions

It may be necessary to check parts of a program independently.
Nondeterminism can be used to over-approximate the behaviour of part of
the system which is not being checked. Rather than calling a complex or
unrelated function, a nondeterministic stub is used. However, separate
calls to the function can return different results, even for the same
inputs. If the function output only depends on its inputs then this can
introduce spurious errors. To avoid this problem, functions whose names
begin with the prefix `__CPROVER_uninterpreted_` are treated as
uninterpreted functions. Their value is non-deterministic but different
invocations will return the same value if their inputs are the same.
Note that uninterpreted functions are not supported by all back-end
solvers.

\subsection man_modelling-assumptions Modeling with Assertions and Assumptions

### Assertions

[Assertions](http://en.wikipedia.org/wiki/Assertion_%28computing%29) are
statements within the program that attempt to capture the programmer's
intent. The ANSI-C standard defines a header file
[assert.h](http://en.wikipedia.org/wiki/Assert.h), which offers a macro
`assert(cond)`. When executing a statement such as

    assert(p!=NULL);

the execution is aborted with an error message if the condition
evaluates to *false*, i.e., if `p` is NULL in the example above. The
CPROVER tools can check the validity of the programmer-annotated
assertions statically. Specifically, the CPROVER tools will check that
the assertions hold for *any* nondeterministic choice that the program
can make. The static assertion checks can be disabled using the
`--no-assertions` command line option.

In addition, there is a CPROVER-specific way to specify assertions,
using the built-in function `__CPROVER_assert`:

    __CPROVER_assert(p!=NULL, "p is not NULL");

The (mandatory) string that is passed as the second argument provides an
informal description of the assertion. It is shown in the list of
properties together with the condition.

The assertion language of the CPROVER tools is identical to the language
used for expressions. Note that \ref man_modelling-nondet
"nondeterminism"
can be exploited in order to check a range of choices. As an example,
the following code fragment asserts that **all** elements of the array
are zero:

    int a[100], i;

    ...

    i=nondet_uint();
    if(i>=0 && i<100)
      assert(a[i]==0);

The nondeterministic choice will guess the element of the array that is
nonzero. The code fragment above is therefore equivalent to

    int a[100], i;

    ...

    for(i=0; i<100; i++)
      assert(a[i]==0);

Future CPROVER releases will support explicit quantifiers with a syntax
that resembles Spec\#:

    __CPROVER_forall { *type identifier* ; *expression* }
    __CPROVER_exists { *type identifier* ; *expression* }

### Assumptions

Assumptions are used to restrict nondeterministic choices made by the
program. As an example, suppose we wish to model a nondeterministic
choice that returns a number from 1 to 100. There is no integer type
with this range. We therefore use \_\_CPROVER\_assume to restrict the
range of a nondeterministically chosen integer:

    unsigned int nondet_uint();

    unsigned int one_to_hundred()
    {
      unsigned int result=nondet_uint();
      __CPROVER_assume(result>=1 && result<=100);
      return result;
    }

The function above returns the desired integer from 1 to 100. You must
ensure that the condition given as an assumption is actually satisfiable
by some nondeterministic choice, or otherwise the model checking step
will pass vacuously.

Also note that assumptions are never retroactive: They only affect
assertions (or other properties) that follow them in program order. This
is best illustrated with an example. In the following fragment, the
assumption has no effect on the assertion, which means that the
assertion will fail:

    x=nondet_uint();
    assert(x==100);
    __CPROVER_assume(x==100);

Assumptions do restrict the search space, but only for assertions that
follow. As an example, the following program will pass:

    int main() {
      int x;

      __CPROVER_assume(x>=1 && x<=100000);

      x*=-1;

      __CPROVER_assert(x<0, "x is negative");
    }

Beware that nondeterminism cannot be used to obtain the effect of
universal quantification in assumptions. As an example,

    int main() {
      int a[10], x, y;

      x=nondet_int();
      y=nondet_int();
      __CPROVER_assume(x>=0 && x<10 && y>=0 && y<10);

      __CPROVER_assume(a[x]>=0);

      assert(a[y]>=0);
    }

fails, as there is a choice of x and y which results in a counterexample
(any choice in which x and y are different).

\subsection man_modelling-pointers Pointer Model

### Pointers in C

C programs (and sometimes C++ programs as well) make intensive use of
pointers in order to decouple program code from specific data. A pointer
variable does not store data such as numbers or letters, but instead
points to a location in memory that hold the relevant data. This section
describes the way the CPROVER tools model pointers.

### Objects and Offsets

The CPROVER tools represent pointers as a pair. The first member of the
pair is the *object* the pointer points to, and the second is the offset
within the object.

In C, objects are simply continuous fragments of memory (this definition
of "object" is not to be confused with the use of the term in
object-oriented programming). Variables of any type are guaranteed to be
stored as one object, irrespectively of their type. As an example, all
members of a struct or array belong to the same object. CPROVER simply
assigns a number to each active object. The object number of a pointer
`p` can be extracted using the expression `__CPROVER_POINTER_OBJECT(p)`.
As a consequence, pointers to different objects are always different,
which is not sound.

The offset (the second member of the pair that forms a pointer) is
relative to the beginning of the object; it uses byte granularity. As an
example, the code fragment

    unsigned array[10];
    char *p;

    p=(char *)(array+1);
    p++;

will result in a pointer with offset 5. The offset of a pointer `p` can
be extracted using the expression `__CPROVER_POINTER_OFFSET(p)`.

### Dereferencing Pointers

The CPROVER tools require that pointers that are dereferenced point to a
valid object. Assertions that check this requirement can be generated
using the option --pointer-check and, if desired, --bounds-check. These
options will ensure that NULL pointers are not dereferenced, and that
dynamically allocated objects have not yet been deallocated.

Furthermore, the CPROVER tools check that dynamically allocated memory
is not deallocated twice. The goto-instrument tool is also able to add
checks for memory leaks, i.e., it detects dynamically allocated objects
that are not deallocated once the program terminates.

The CPROVER tools support pointer typecasts. Most casts are supported,
with the following exceptions:

1.  One notable exception is that pointers can only be accessed using a
    pointer type. The conversion of a pointer into an integer-type using
    a pointer typecast is not supported.

2.  Casts from integers to pointers yield a pointer that is either NULL
    (if the integer is zero) or that point into a special array for
    modeling [memory-mapped
    I/O](http://en.wikipedia.org/wiki/Memory-mapped_I/O). Such pointers
    are assumed not to overlap with any other objects. This is, of
    course, only sound if a corresponding range check is instrumented.

3.  Accesses to arrays via pointers that have the array subtype need to
    be well-aligned.

### Pointers in Open Programs

It is frequently desired to validate an open program, i.e., a fragment
of a program. Some variables are left undefined. In case an undefined
pointer is dereferenced, CBMC assumes that the pointer points to a
separate object of appropriate type with unbounded size. The object is
assumed not to alias with any other object. This assumption may
obviously be wrong in specific extensions of the program.

\subsection man_modelling-floating-point Floating Point

The CPROVER tools support bit-accurate reasoning about IEEE-754
floating-point and fixed-point arithmetic. The C standard contains a
number of areas of implementation-defined behaviour with regard to
floating-point arithmetic:

-   CPROVER supports C99 Appendix F, and thus, the `__STD_IEC_559__`
    macro is defined. This means that the C `float` data type maps to
    IEEE 754 `binary32` and `double` maps to `binary64` and operations
    on them are as specified in IEEE 754.

-   `long double` can be configured to be `binary64`, `binary128`
    (quad precision) or a 96 bit type with 15 exponent bits and 80
    significant bits. The last is an approximation of Intel's x87
    extended precision double data type. As the C standard allows a
    implementations a fairly wide set of options for `long double`, it
    is best avoided for both portable code and bit-precise analysis. The
    default is to match the build architecture as closely as possible.

-   In CPROVER, floating-point expressions are evaluated at the 'natural
    precision' (the greatest of the arguments) and not at a
    higher precision. This corresponds to `FLT_EVAL_METHOD` set to `0`.
    Note that this is a different policy to some platforms (see below).

-   Expression contraction (for example, converting `x * y +   c` to
    `fma(x,y,c)`) is not performed. In effect, the `FP_CONTRACT` pragma
    is always off.

-   Constant expressions are evaluated at \`run' time wherever possible
    and so will respect changes in the rounding mode. In effect, the
    `FENV_ACCESS` pragma is always off. Note that floating point
    constants are treated as doubles (unless they are followed by `f`
    when they are float) as specified in the C standard. `goto-cc`
    supports `-fsingle-precision-constant`, which allows
    the (non-standard) treatment of constants as floats.

-   Casts from int to float and float to float make use of the current
    rounding mode. Note that the standard requires that casts from float
    to int use round-to-zero (i.e. truncation).

### x86 and Other Platform-specific Issues

Not all platforms have the same implementation-defined behaviour as
CPROVER. This can cause mismatches between the verification environment
and the execution environment. If this occurs, check the compiler manual
for the choices listed above. There are two common cases that can cause
these problems: 32-bit x86 code and the use of unsafe optimisations.

Many compilers that target 32-bit x86 platforms employ a different
evaluation method. The extended precision format of the x87 unit is used
for all computations regardless of their native precision. Most of the
time, this results in more accurate results and avoids edge cases.
However, it can result in some obscure and difficult to debug behaviour.
Checking if the `FLT_EVAL_METHOD` macro is non-zero (for these platforms
it will typically be 2), should warn of these problems. Changing the
compiler flags to use the SSE registers will resolve many of them, give
a more standards-compliant platform and will likely perform better. Thus
it is *highly* recommended. Use `-msse2 -mfpmath=sse` to enable this
option for GCC. Visual C++ does not have an option to force the
exclusive use of SSE instructions, but `/arch:SSE2` will pick SSE
instructions "when it \[the compiler\] determines that it is faster to
use the SSE/SSE2 instructions" and is thus better than `/arch:IA32`,
which exclusively uses the x87 unit.

The other common cause of discrepancy between CPROVER results and the
actual platform are the use of unsafe optimisations. Some higher
optimisation levels enable transformations that are unsound with respect
to the IEEE-754 standard. Consult the compiler manual and disable any
optimisations that are described as unsafe (for example, the GCC options
`-ffast-math`). The options `-ffp-contract=off` (which replaces
`-mno-fused-madd`), `-frounding-math` and `-fsignaling-nans` are needed
for GCC to be strictly compliant with IEEE-754.

### Rounding Mode

CPROVER supports the four rounding modes given by IEEE-754 1985; round
to nearest (ties to even), round up, round down and round towards zero.
By default, round to nearest is used. However, command line options
(`--round-to-zero`, etc.) can be used to over-ride this. If more control
is needed, CPROVER has models of `fesetround` (for POSIX systems) and
`_controlfp` (for Windows), which can be used to change the rounding
mode during program execution. Furthermore, the inline assembly commands
fstcw/fnstcw/fldcw (on x86) can be used.

The rounding mode is stored in the (thread local) variable
`__CPROVER_rounding_mode`, but users are strongly advised not to use
this directly.

### Math Library

CPROVER implements some of `math.h`, including `fabs`, `fpclassify` and
`signbit`. It has very limited support for elementary functions. Care
must be taken when verifying properties that are dependent on these
functions as the accuracy of implementations can vary considerably. The
C compilers can (and many do) say that the accuracy of these functions
is unknown.

### Fixed-point Arithmetic

CPROVER also has support for fixed-point types. The `--fixedbv` flag
switches `float`, `double` and `long   double` to fixed-point types. The
length of these types is platform specific. The upper half of each type
is the integer component and the lower half is the fractional part.


\section man_hard-soft Hardware and Software Equivalence and Co-Verification

\subsection man_hard-soft-introduction Introduction

A common hardware design approach employed by many companies is to first
write a quick prototype that behaves like the planned circuit in a
language like ANSI-C. This program is then used for extensive testing
and debugging, in particular of any embedded software that will later on
be shipped with the circuit. An example is the hardware of a cell phone
and its software. After testing and debugging of the program, the actual
hardware design is written using hardware description languages like
[VHDL](http://en.wikipedia.org/wiki/VHDL) or
[Verilog](http://en.wikipedia.org/wiki/Verilog).

Thus, there are two implementations of the same design: one written in
ANSI-C, which is written for simulation, and one written in register
transfer level HDL, which is the actual product. The ANSI-C
implementation is usually thoroughly tested and debugged.

Due to market constraints, companies aim to sell the chip as soon as
possible, i.e., shortly after the HDL implementation is designed. There
is usually little time for additional debugging and testing of the HDL
implementation. Thus, an automated, or nearly automated way of
establishing the consistency of the HDL implementation is highly
desirable.

This motivates the verification problem: we want to verify the
consistency of the HDL implementation, i.e., the product, [using the
ANSI-C implementation as a
reference](http://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=936243&userType=inst).
Es­ta­bli­shing the consistency does not re­quire a formal
specification. However, formal methods to verify either the hardware or
software design are still desirable.

### Related Work

There have been several attempts in the past to tackle the problem.
[Semeria et al.](http://portal.acm.org/citation.cfm?id=513951) describe
a tool for verifying the combinational equivalence of RTL-C and an HDL.
They translate the C code into HDL and use standard equivalence checkers
to establish the equivalence. The C code has to be very close to a
hardware description (RTL level), which implies that the source and
target have to be implemented in a very similar way. There are also
variants of C specifically for this purpose. The [SystemC
standard](http://en.wikipedia.org/wiki/SystemC) defines a subset of C++
that can be used for synthesis. Further variants of ANSI-C for
specifying hardware are SpecC and Handel C, among others.

The concept of verifying the equivalence of a software implementation
and a synchronous transition system was introduced by [Pnueli, Siegel,
and Shtrichman](http://www.springerlink.com/content/ah5lpxaagrjp8ax2/).
The C program is re­quired to be in a very specific form, since a
mechanical translation is assumed.

In 2000, [Currie, Hu, and
Rajan](http://doi.acm.org/10.1145/337292.337339) transform DSP assembly
language into an equation for the Stanford Validity Checker. The
symbolic execution of programs for comparison with RTL is now common
practice.

The previous work focuses on a small subset of ANSI-C that is
particularly close to register transfer language. Thus, the designer is
often re­quired to rewrite the C program manually in order to comply
with these constraints. We extend the methodology to handle the full set
of ANSI-C language features. This is a challenge in the presence of
complex, dynamic data structures and pointers that may dynamically point
to multiple objects. Furthermore, our methodology allows arbitrary loop
constructs.

### Further Material

We provide a small \ref man_hard-soft-tutorial "tutorial" and a
description on
\ref man_hard-soft-inputs "how to synchronize inputs between the C model and the Verilog model".
There is also a collection of
[benchmark problems](http://www.cprover.org/hardware/sequential-equivalence/)
available.

Further Reading

-   [Hardware Verification using ANSI-C Programs as a
    Reference](http://www-2.cs.cmu.edu/~svc/papers/view-publications-ck03.html)
-   [Behavioral Consistency of C and Verilog Programs Using Bounded
    Model Checking](http://www-2.cs.cmu.edu/~svc/papers/view-publications-cky03.html)
-   [A Tool for Checking ANSI-C
    Programs](http://www-2.cs.cmu.edu/~svc/papers/view-publications-ckl2004.html)
-   [Checking Consistency of C and Verilog using Predicate Abstraction
    and Induction](http://www.kroening.com/publications/view-publications-kc2004.html)


\subsection man_hard-soft-tutorial Tutorial

### Verilog vs. ANSI-C

We assume that CBMC is installed on your system. If not so, follow
\ref man_install-cbmc "these instructions".

The following Verilog module implements a 4-bit counter
(counter.v):

    module top(input clk);

      reg [3:0] counter;

      initial counter=0;

      always @(posedge clk)
        counter=counter+1;

    endmodule

HW-CBMC can take Verilog modules as the one above as additional input.
Similar as in co-simulation, the data in the Verilog modules is
available to the C program by means of global variables. For the example
above, the following C fragment shows the definition of the variable
that holds the value of the `counter` register:

    struct module_top {
      unsigned int counter;
    };

    extern struct module_top top;

Using this definition, the value of the `counter` register in the
Verilog fragment above can be accessed as `top.counter`. Please note
that the name of the variable **must** match the name of the top module.
The C program only has a view of one state of the Verilog model. The
Verilog model makes a transition once the function `next_timeframe()` is
called.

As CBMC performs Bounded Model Checking, the number of timeframes
available for analysis must be bounded (SATABS). As it is desirable to
change the bound to adjust it to the available computing capacity, the
bound is given on the command line and not as part of the C program.
This makes it easy to use only one C program for arbitrary bounds. The
actual bound is available in the C program using the following
declaration:

    extern const unsigned int bound;

Also note that the fragment above declares a constant variable of struct
type. Thus, the C program can only read the trace values and is not able
to modify them. We will later on describe how to drive inputs of the
Verilog module from within the C program.

As described in previous chapters, assertions can be used to verify
properties of the Verilog trace. As an example, the following program
checks two values of the trace of the counter module (counter.c):

    void next_timeframe();

    struct module_top {
      unsigned int counter;
    };

    extern struct module_top top;

    int main() {
      next_timeframe();
      next_timeframe();
      assert(top.counter==2);
      next_timeframe();
      assert(top.counter==3);
    }

The following CBMC command line checks these assertions with a bound of
20:

    hw-cbmc counter.c counter.v --module top --bound 20

Note that a specific version of CBMC is used, called `hw-cbmc`. The
module name given must match the name of the module in the Verilog file.
Multiple Verilog files can be given on the command line.

The `--bound` parameter is not to be confused with the `--unwind`
parameter. While the `--unwind` parameter specifies the maximum
unwinding depth for loops within the C program, the `--bound` parameter
specifies the number of times the transition relation of the Verilog
module is to be unwound.

### Counterexamples

For the given example, the verification is successful. If the first
assertion is changed to

    assert(top.counter==10);

and the bound on the command line is changed to 6, CBMC will produce a
counterexample. CBMC produces two traces: One for the C program, which
matches the traces described earlier, and a separate trace for the
Verilog module. The values of the registers in the Verilog module are
also shown in the C trace as part of the initial state.

    Initial State
    ----------------------------------------------------
      bound=6 (00000000000000000000000000000110)
      counter={ 0, 1, 2, 3, 4, 5, 6 }

    Failed assertion: assertion line 6 function main

    Transition system state 0
    ----------------------------------------------------
      counter=0 (0000)

    Transition system state 1
    ----------------------------------------------------
      counter=1 (0001)

    Transition system state 2
    ----------------------------------------------------
      counter=2 (0010)

    Transition system state 3
    ----------------------------------------------------
      counter=3 (0011)

    Transition system state 4
    ----------------------------------------------------
      counter=4 (0100)

    Transition system state 5
    ----------------------------------------------------
      counter=5 (0101)

    Transition system state 6
    ----------------------------------------------------
      counter=6 (0110)

### Using the Bound

The following program is using the bound variable to check the counter
value in all cycles:

    void next_timeframe();
    extern const unsigned int bound;

    struct module_top {
      unsigned int counter;
    };

    extern struct module_top top;

    int main() {
      unsigned cycle;

      for(cycle=0; cycle<bound; cycle++) {
        assert(top.counter==(cycle & 15));
        next_timeframe();
      }
    }

CBMC performs bounds checking, and restricts the number of times that
`next_timeframe()` can be called. SATABS does not re­quire a bound, and
thus, `next_timeframe()` can be called arbitrarily many times.


\subsection man_hard-soft-mapping Mapping Variables

### Mapping Variables within the Module Hierarchy

Verilog modules are hierarchical. The `extern` declarations shown above
only allow reading the values of signals and registers that are in the
top module. In order to read values from sub-modules, CBMC uses
structures.

As an example, consider the following Verilog file
(heirarchy.v):

    module counter(input clk, input [7:0] increment);

      reg [7:0] counter;

      initial counter=0;

      always @(posedge clk)
        counter=counter+increment;

    endmodule

    module top(input clk);

      counter c1(clk, 1);
      counter c2(clk, 2);

    endmodule

The file has two modules: a top module and a counter module. The counter
module is instantiated twice within the top module. A reference to the
register `counter` within the C program would be ambiguous, as the two
module instances have separate instances of the register. CBMC and
SATABS use the following data structures for this example:

    void next_timeframe();
    extern const unsigned int bound;

    struct counter {
      unsigned char increment;
      unsigned char counter;
    };

    struct module_top {
      struct module_counter c1, c2;
    };

    extern struct module_top top;

    int main() {
      next_timeframe();
      next_timeframe();
      next_timeframe();
      assert(top.c1.counter==3);
      assert(top.c2.counter==6);
    }

The `main` function reads both counter values for cycle 3. A deeper
hierarchy (modules in modules) is realized by using additional structure
members. Writing these data structures for large Verilog designs is
error prone, and thus, HW-CBMC can generate them automatically. The
declarations above are generated using the command line

    hw-cbmc --gen-interface --module top hierarchy.v

### Mapping Verilog Vectors to Arrays or Scalars

In Verilog, a definition such as

    wire [31:0] x;

can be used for arithmetic (as in `x+10`) and as array of Booleans (as
in `x[2]`). ANSI-C does not allow both, so when mapping variables from
Verilog to C, the user has to choose one option for each such variable.
As an example, the C declaration

    unsigned int x;

will allow using `x` in arithmetic expressions, while the C declaration

    __CPROVER_bool x[32];

will allow accessing the individual bits of `x` using the syntax
`x[bit]`. The `--gen-interface` option of HW-CBMC will generate the
first variant if the vector has the same size as one of the standard
integer types, and will use the `__CPROVER_bitvector[]` type if not
so. This choice can be changed by adjusting the declaration accordingly.
Note that both SpecC and SystemC offer bit-extraction operators, which
means that it unnecessary to use the declaration as array in order to
access individual bits of a vector.

\subsection man_hard-soft-inputs Synchronizing Inputs

### Driving Primary Inputs

The examples in the \ref man_hard-soft-tutorial "tutorial" are trivial
in the sense that the model has only one possible trace. The initial
state is deterministic, and there is only one possible transition, so
the verification problem can be solved by testing a single run. In
contrast, consider the following Verilog module:

    module top(input clk, input i);

      reg [3:0] counter;

      initial counter=0;

      always @(posedge clk)
        if(i)
          counter=counter+1;

    endmodule

The module above has an input named `i`. The top-level inputs of the
Verilog design have to be generated by the C program. This is done by
assigning the desired values to the corresponding struct member, and
then calling the `set_inputs()` function before calling
`next_timeframe()`. Consider the following example:

    void next_timeframe();
    void set_inputs();
    extern const unsigned int bound;

    struct module_top {
      unsigned int counter;
      _Bool i;
    };

    extern struct module_top top;

    int main() {
      assert(top.counter==0);

      top.i=1;
      set_inputs(); next_timeframe();
      assert(top.counter==1);

      top.i=1;
      set_inputs(); next_timeframe();
      assert(top.counter==2);

      top.i=0;
      set_inputs(); next_timeframe();
      assert(top.counter==2);
    }

As an example, consider a Verilog module that has a signal `reset` as an
input, which is active-low. The following C fragment drives this input
to be active in the first cycle, and not active in any subsequent cycle:

      top.resetn=0;
      set_inputs(); next_timeframe();

      for(i=1; i<bound; i++) {
        top.resetn=1;
        set_inputs(); next_timeframe();
      }

Note that the value of the input must be set *before* calling
`next_timeframe()`. The effect of the input values on values derived in
a combinatorial way is immediately visible. The effect on clocked values
becomes visible in the next time frame.

### Using Nondeterminism

The examples above use particular, constant values to drive the primary
inputs. In order to check the behavior of the Verilog model for more
than one specific input, use \ref man_modelling-nondet "nondeterminism".


\section man_instrumentation Build Systems, Libraries, and Instrumentation

\subsection man_instrumentation-libraries Build Systems and Libraries

### The Problem

Similar to unit testing, the model checking approach requires the user
to clearly define what parts of the program should be tested and what
the behaviour of these parts is. This requirement has following reasons:

-   Despite recent advances, the size of the programs that model
    checkers can cope with is still restricted.

-   Typically, you want to verify *your* program and not the libraries
    or the operating that it uses (the correctness of these libraries
    and the OS us usually addressed separately).

-   CBMC and SATABS cannot verify binary libraries.

-   CBMC and SATABS does not provide a model for the hardware (e.g.,
    hard disk, input/output devices) the tested program runs on. Since
    CBMC and SATABS are supposed to examine the behavior of the tested
    program for **all** possible inputs and outputs, it is reasonable to
    model input and output by means of non-deterministic choice.

### Further Reading

Existing software projects usually do not come in a single source file
that may simply be passed to a model checker, but is a collection of
files held together by a build system. The extraction of models from
such a build system using goto-cc is described
\ref man_instrumentation-goto-cc "here".

\subsection man_instrumentation-goto-cc Integration into Build Systems with goto-cc

Existing software projects usually do not come in a single source file
that may simply be passed to a model checker. They rather come in a
multitude of source files in different directories and refer to external
libraries and system-wide options. A *build system* then collects the
configuration options from the system and compiles the software
according to build rules.

The most prevalent build tool on Unix (-based) systems surely is the
`make` utility. This tool uses build rules given in a *Makefile* that
comes with the software sources. Running software verification tools on
projects like these is greatly simplified by a compiler that first
collects all the necessary models into a single model file.
[goto-cc](http://www.cprover.org/goto-cc/) is such a model file
extractor, which can seamlessly replace `gcc` and `cl.exe` in Makefiles.
The normal build system for the project may be used to build the
software, but the outcome will be a model file with suitable detail for
verification, as opposed to a flat executable program. Note that goto-cc
comes in different variants depending on the compilation environment.
These variants are described [here](goto-cc-variants.shtml).

### Example: Building wu-ftpd

This example assumes a Unix-like machine.

1.  Download the sources of wu-ftpd from
    [here](ftp://ftp.wu-ftpd.org/pub/wu-ftpd/wu-ftpd-current.tar.gz).

2.  Unpack the sources by running ` tar xfz wu-ftpd-current.tar.gz`

3.  Change to the source directory, by entering, e.g.,
    `cd wu-ftpd-2.6.2`

4.  Configure the project for verification by running

    `./configure YACC=byacc CC=goto-cc --host=none-none-none`

5.  Build the project by running `make`. This creates multiple model
    files in the `src` directory. Among them is a model for the main
    executable `ftpd`.

6.  Run a model-checker, e.g., CBMC, on the model file:

        `cbmc src/ftpd`

    CBMC automatically recognizes that the file is a goto binary.

### Important Notes

More elaborate build or configuration scripts often make use of features
of the compiler or the system library to detect configuration options
automatically, e.g., in a `configure` script. Replacing `gcc` by goto-cc
at this stage may confuse the script, or detect wrong options. For
example, missing library functions do not cause goto-cc to throw an
error (only to issue a warning). Because of this, configuration scripts
sometimes falsely assume the availability of a system function or
library.

In the case of this or similar problems, it is more advisable to
configure the project using the normal routine, and replacing the
compiler setting manually in the generated Makefiles, e.g., by replacing
lines like `CC=gcc` by `CC=goto-cc`.

A helpful command that accomplishes this task successfully for many
projects is the following:

    for i in `find . -name Makefile`; do   sed -e 's/^\(\s*CC[ \t]*=\)\(.*$\)/\1goto-cc/g' -i $i done

Here are additional examples on how to use goto-cc:

-   \ref man_goto-cc-linux "Linux Kernel"
-   \ref man_goto-cc-apache "Apache HTTPD"

A description of how to integrate goto-cc into Microsoft's Visual Studio
is \ref man_instrumentation-vs "here".

### Linking Libraries

Some software projects come with their own libraries; also, the goal may
be to analyze a library by itself. For this purpose it is possible to
use goto-cc to link multiple model files into a library of model files.
An object file can then be linked against this model library. For this
purpose, goto-cc also features a linker mode.

To enable this linker mode, create a link to the goto-cc binary by the
name of goto-ld (Linux and Mac) or copy the goto-cc binary to
goto-link.exe (Windows). The goto-ld tool can now be used as a seamless
replacement for the `ld` tool present on most Unix (-based) systems and
for the `link` tool on Windows.

The default linker may need to be replaced by `goto-ld` or
`goto-link.exe` in the build script, which can be achieved in much the
same way as replacing the compiler.


\subsection man_instrumentation-vs Integration into Visual Studio 2008 to 2012

Visual Studio version 2008 onwards comes with a new XML-based build
system called
[MSBuild](http://msdn.microsoft.com/en-us/library/ms171452.aspx).
The MSBuild system is also activated when triggering a build from the
Visual Studio GUI. The project files created by the Visual Studio GUI
are used as input by the MSBuild tool.

The MSBuild system can be used to generate goto-binaries from your
Visual Studio project as follows:

1.  Install the `goto-cl.exe` and `goto-link.exe` binaries in some
    directory that is contained in the PATH environment variable.

2.  Add a configuration for the goto-cc build for your project in the
    configuration manager, named "goto-cc".

3.  Open the Visual Studio Command Prompt (in the Tools menu).

4.  Locate the directory that contains the project. Change into this
    directory using "CD".

5.  Type

        msbuild /p:CLToolExe=goto-cl.exe /p:LinkToolExe=goto-link.exe    /p:Flavor=goto-cc /p:Platform=x86

    The platform can be adjusted as required; the "Flavor" given should
    match the configuration that was created earlier.

Note that the recent versions of goto-cc also support file names with
non-ASCII (Unicode) characters on Windows platforms.

\subsection man_instrumentation-goto-cc-variants Variants of goto-cc

The goto-cc utility comes in several variants, summarised in the
following table.

Executable    | Environment                                                             | Preprocessor
--------------|-------------------------------------------------------------------------|-------
  goto-cc     | [gcc](http://gcc.gnu.org/) (control-flow graph only)                    | gcc -E
  goto-gcc    | [gcc](http://gcc.gnu.org/) ("hybrid" executable)                        | gcc -E
  goto-armcc  | [ARM RVDS](http://arm.com/products/tools/software-tools/rvds/index.php) | armcc -E
  goto-cl     | [Visual Studio](http://www.microsoft.com/visualstudio/)                 | cl /E
  goto-cw     | [Freescale CodeWarrior](http://www.freescale.com/webapp/sps/site/homepage.jsp?code=CW_HOME) | mwcceppc

The primary difference between the variants is the preprocessor called.
Furthermore, the language recognized varies slightly. The variants can
be obtained by simply renaming the goto-cc executable. On Linux/MacOS,
the variants can be obtained by creating a symbolic link.

The "hybrid" executables contain both the control-flow graph for
verification purposes and the usual, executable machine code.

\subsection man_instrumentation-architecture Architectural Settings

The behavior of a C/C++ program depends on a number of parameters that
are specific to the architecture the program was compiled for. The three
most important architectural parameters are:

-   The width of the various scalar types; e.g., compare the value of
    `sizeof(long int)` on various machines.
-   The width of pointers; e.g., compare the value of `sizeof(int *)` on
    various machines.
-   The [endianness](http://en.wikipedia.org/wiki/Endianness) of
    the architecture.

In general, the CPROVER tools attempt to adopt the settings of the
particular architecture the tool itself was compiled for. For example,
when running a 64 bit binary of CBMC on Linux, the program will be
processed assuming that `sizeof(long int)==8`.

As a consequence of these architectural parameters, you may observe
different verification results for an identical program when running
CBMC on different machines. In order to get consistent results, or when
aiming at validating a program written for a different platform, the
following command-line arguments can be passed to the CPROVER tools:

-   The word-width can be set with `--16`, `--32`, `--64`.
-   The endianness can be defined with `--little-endian` and
    `--big-endian`.

When using a goto binary, CBMC and the other tools read the
configuration from the binary, i.e., the setting when running goto-cc is
the one that matters; the option given to the model checker is ignored
in this case.

In order to see the effect of the options `--16`, `--32` and `--64`,
pass the following program to CBMC:

    #include <stdio.h>
    #include <assert.h>

    int main() {
      printf("sizeof(long int): %d\n", (int)sizeof(long int));
      printf("sizeof(int *): %d\n", (int)sizeof(int *));
      assert(0);
    }

The counterexample trace contains the strings printed by the `printf`
command.

The effects of endianness are more subtle. Try the following program
with `--big-endian` and `--little-endian`:

    #include <stdio.h>
    #include <assert.h>

    int main() {
      int i=0x01020304;
      char *p=(char *)&i;
      printf("Bytes of i: %d, %d, %d, %d\n", p[0], p[1], p[2], p[3]);
      assert(0);
    }


\subsection man_instrumentation-properties Property Instrumentation

### Properties

We have mentioned *properties* several times so far, but we never
explained *what* kind of properties CBMC and SATABS can verify. We cover
this topic in more detail in this section.

Both CBMC and SATABS use
[assertions](http://en.wikipedia.org/wiki/Assertion_(computing)) to
specify program properties. Assertions are properties of the state of
the program when the program reaches a particular program location.
Assertions are often written by the programmer by means of the `assert`
macro.

In addition to the assertions written by the programmer, assertions for
specific properties can also be generated automatically by CBMC and
SATABS, often relieving the programmer from writing "obvious"
assertions.

CBMC and SATABS come with an assertion generator called
`goto-instrument`, which performs a conservative [static
analysis](http://en.wikipedia.org/wiki/Static_code_analysis) to
determine program locations that potentially contain a bug. Due to the
imprecision of the static analysis, it is important to emphasize that
these generated assertions are only *potential* bugs, and that the Model
Checker first needs to confirm that they are indeed genuine bugs.

The assertion generator can generate assertions for the verification of
the following properties:

-   **Buffer overflows.** For each array access, check whether the upper
    and lower bounds are violated.
-   **Pointer safety.** Search for `NULL`-pointer dereferences or
    dereferences of other invalid pointers.

-   **Division by zero.** Check whether there is a division by zero in
    the program.

-   **Not-a-Number.** Check whether floating-point computation may
    result in [NaNs](http://en.wikipedia.org/wiki/NaN).

-   **Unitialized local.** Check whether the program uses an
    uninitialized local variable.

-   **Data race.** Check whether a concurrent program accesses a shared
    variable at the same time in two threads.

We refrain from explaining the properties above in detail. Most of them
relate to behaviors that are left undefined by the respective language
semantics. For a discussion on why these behaviors are usually very
undesirable, read [this](http://blog.regehr.org/archives/213) blog post
by John Regehr.

All the properties described above are *reachability* properties. They
are always of the form

"*Is there a path through the program such that property ... is
violated?*"

The counterexamples to such properties are always program paths. Users
of the Eclipse plugin can step through these counterexamples in a way
that is similar to debugging programs. The installation of this plugin
is explained \ref man_install-eclipse "here".

### Using goto-instrument

The goto-instrument static analyzer operates on goto-binaries, which is
a binary representation of control-flow graphs. The goto-binary is
extracted from program source code using goto-cc, which is explained
\ref man_instrumentation-goto-cc "here". Given a goto-program,
goto-instrument operates as follows:

1.  A goto-binary is read in.
2.  The specified static analyses are performed.
3.  Any potential bugs found are transformed into corresponding
    assertions, and are added into the program.
4.  A new goto-binary (with assertions) is written to disc.

As an example, we begin with small C program we call `expr.c` (taken
from [here](http://www.spinroot.com/uno/)):

    int *ptr;

    int main(void) {
      if (ptr)
        *ptr = 0;
      if (!ptr)
        *ptr = 1;
    }

The program contains an obvious NULL-pointer dereference. We first
compile the example program with goto-cc and then instrument the
resulting goto-binary with pointer checks.

    goto-cc expr.c -o in.gb   goto-instrument in.gb out.gb --pointer-check

We can now get a list of the assertions that have been generated as
follows:

    goto-instrument out.gb --show-properties

Using either CBMC or SATABS on `out.gb`, we can obtain a counterexample
trace for the NULL-pointer dereference:

    cbmc out.gb

The goto-instrument program supports the following checks:

Flag                         |  Check
-----------------------------|----------------------------------------------
`--no-assertions`            |  ignore user assertions
`--bounds-check`             |  add array bounds checks
`--div-by-zero-check`        |  add division by zero checks
`--pointer-check`            |  add pointer checks
`--signed-overflow-check`    |  add arithmetic over- and underflow checks
`--unsigned-overflow-check`  |  add arithmetic over- and underflow checks
`--undefined-shift-check`    |  add range checks for shift distances
`--nan-check`                |  add floating-point NaN checks
`--uninitialized-check`      |  add checks for uninitialized locals (experimental)
`--error-label label`        |  check that given label is unreachable

\subsection man_instrumentation-api The CPROVER API Reference

The following sections summarize the functions available to programs
that are passed to the CPROVER tools.

### Functions

#### \_\_CPROVER\_assume, \_\_CPROVER\_assert, assert

    void __CPROVER_assume(_Bool assumption);
    void __CPROVER_assert(_Bool assertion, const char *description);
    void assert(_Bool assertion);

The function **\_\_CPROVER\_assume** adds an expression as a constraint
to the program. If the expression evaluates to false, the execution
aborts without failure. More detail on the use of assumptions is in the
section on [Assumptions and Assertions](modeling-assertions.shtml).

#### \_\_CPROVER\_same\_object, \_\_CPROVER\_POINTER\_OBJECT, \_\_CPROVER\_POINTER\_OFFSET, \_\_CPROVER\_DYNAMIC\_OBJECT

    _Bool __CPROVER_same_object(const void *, const void *);
    unsigned __CPROVER_POINTER_OBJECT(const void *p);
    signed __CPROVER_POINTER_OFFSET(const void *p);
    _Bool __CPROVER_DYNAMIC_OBJECT(const void *p);

The function **\_\_CPROVER\_same\_object** returns true if the two
pointers given as arguments point to the same object. The function
**\_\_CPROVER\_POINTER\_OFFSET** returns the offset of the given pointer
relative to the base address of the object. The function
**\_\_CPROVER\_DYNAMIC\_OBJECT** returns true if the pointer passed as
arguments points to a dynamically allocated object.

#### \_\_CPROVER\_is\_zero\_string, \_\_CPROVER\_zero\_string\_length, \_\_CPROVER\_buffer\_size

    _Bool __CPROVER_is_zero_string(const void *);
    __CPROVER_size_t __CPROVER_zero_string_length(const void *);
    __CPROVER_size_t __CPROVER_buffer_size(const void *);

#### \_\_CPROVER\_initialize

    void __CPROVER_initialize(void);

The function **\_\_CPROVER\_initialize** computes the initial state of
the program. It is called prior to calling the main procedure of the
program.

#### \_\_CPROVER\_input, \_\_CPROVER\_output

    void __CPROVER_input(const char *id, ...);
    void __CPROVER_output(const char *id, ...);

The functions **\_\_CPROVER\_input** and **\_\_CPROVER\_output** are
used to report an input or output value. Note that they do not generate
input or output values. The first argument is a string constant to
distinguish multiple inputs and outputs (inputs are typically generated
using nondeterminism, as described [here](modeling-nondet.shtml)). The
string constant is followed by an arbitrary number of values of
arbitrary types.

#### \_\_CPROVER\_cover

    void __CPROVER_cover(_Bool condition);

This statement defines a custom coverage criterion, for usage with the
[test suite generation feature](cover.shtml).

#### \_\_CPROVER\_isnan, \_\_CPROVER\_isfinite, \_\_CPROVER\_isinf, \_\_CPROVER\_isnormal, \_\_CPROVER\_sign

    _Bool __CPROVER_isnan(double f);
    _Bool __CPROVER_isfinite(double f);
    _Bool __CPROVER_isinf(double f);
    _Bool __CPROVER_isnormal(double f);
    _Bool __CPROVER_sign(double f);

The function **\_\_CPROVER\_isnan** returns true if the double-precision
floating-point number passed as argument is a
[NaN](http://en.wikipedia.org/wiki/NaN).

The function **\_\_CPROVER\_isfinite** returns true if the
double-precision floating-point number passed as argument is a finite
number.

This function **\_\_CPROVER\_isinf** returns true if the
double-precision floating-point number passed as argument is plus or
minus infinity.

The function **\_\_CPROVER\_isnormal** returns true if the
double-precision floating-point number passed as argument is a normal
number.

This function **\_\_CPROVER\_sign** returns true if the double-precision
floating-point number passed as argument is negative.

#### \_\_CPROVER\_abs, \_\_CPROVER\_labs, \_\_CPROVER\_fabs, \_\_CPROVER\_fabsl, \_\_CPROVER\_fabsf

    int __CPROVER_abs(int x);
    long int __CPROVER_labs(long int x);
    double __CPROVER_fabs(double x);
    long double __CPROVER_fabsl(long double x);
    float __CPROVER_fabsf(float x);

These functions return the absolute value of the given argument.

#### \_\_CPROVER\_array\_equal, \_\_CPROVER\_array\_copy, \_\_CPROVER\_array\_set

    _Bool __CPROVER_array_equal(const void array1[], const void array2[]);
    void __CPROVER_array_copy(const void dest[], const void src[]);
    void __CPROVER_array_set(const void dest[], value);

The function **\_\_CPROVER\_array\_equal** returns true if the values
stored in the given arrays are equal. The function
**\_\_CPROVER\_array\_copy** copies the contents of the array **src** to
the array **dest**. The function **\_\_CPROVER\_array\_set** initializes
the array **dest** with the given value.

#### Uninterpreted Functions

Uninterpreted functions are documented \ref man_modelling-nondet "here".

### Predefined Types and Symbols

#### \_\_CPROVER\_bitvector

    __CPROVER_bitvector [ expression ]

This type is only available in the C frontend. It is used to specify a
bit vector with arbitrary but fixed size. The usual integer type
modifiers **signed** and **unsigned** can be applied. The usual
arithmetic promotions will be applied to operands of this type.

#### \_\_CPROVER\_floatbv

    __CPROVER_floatbv [ expression ] [ expression ]

This type is only available in the C frontend. It is used to specify an
IEEE-754 floating point number with arbitrary but fixed size. The first
parameter is the total size (in bits) of the number, and the second is
the size (in bits) of the mantissa, or significand (not including the
hidden bit, thus for single precision this should be 23).

#### \_\_CPROVER\_fixedbv

     __CPROVER_fixedbv [ expression ] [ expression ]

This type is only available in the C frontend. It is used to specify a
fixed-point bit vector with arbitrary but fixed size. The first
parameter is the total size (in bits) of the type, and the second is the
number of bits after the radix point.

#### \_\_CPROVER\_size\_t

The type of sizeof expressions.

#### \_\_CPROVER\_rounding\_mode

     extern int __CPROVER_rounding_mode;

This variable contains the IEEE floating-point arithmetic rounding mode.

#### \_\_CPROVER\_constant\_infinity\_uint

This is a constant that models a large unsigned integer.

#### \_\_CPROVER\_integer, \_\_CPROVER\_rational

**\_\_CPROVER\_integer** is an unbounded, signed integer type.
**\_\_CPROVER\_rational** is an unbounded, signed rational number type.

#### \_\_CPROVER\_memory

    extern unsigned char __CPROVER_memory[];

This array models the contents of integer-addressed memory.

#### \_\_CPROVER::unsignedbv&lt;N&gt; (C++ only)

This type is the equivalent of **unsigned \_\_CPROVER\_bitvector\[N\]**
in the C++ front-end.

#### \_\_CPROVER::signedbv&lt;N&gt; (C++ only)

This type is the equivalent of **signed \_\_CPROVER\_bitvector\[N\]** in
the C++ front-end.

#### \_\_CPROVER::fixedbv&lt;N&gt; (C++ only)

This type is the equivalent of **\_\_CPROVER\_fixedbv\[N,m\]** in the
C++ front-end.

### Concurrency

Asynchronous threads are created by preceding an instruction with a
label with the prefix **\_\_CPROVER\_ASYNC\_**.

\subsection man_goto-cc-linux goto-cc: Extracting Models from the Linux Kernel

The Linux kernel code consists of more than 11 million lines of
low-level C and is frequently used to evaluate static analysis
techniques. In the following, we show how to extract models from Linux
2.6.39.

1.  First of all, you will need to make sure you have around 100 GB of
    free disc space available.

2.  Download the Kernel sources at
    <http://www.kernel.org/pub/linux/kernel/v2.6/linux-2.6.39.tar.bz2>.

3.  Now do

      `bunzip2 linux-2.6.39.tar.bz2`\
      `tar xvf linux-2.6.39.tar`\
      `cd linux-2.6.39`

4.  Now ensure that you can actually compile a kernel by doing

      `make defconfig`\
      `make`

    These steps need to succeed before you can try to extract models
    from the kernel.

5.  Now compile [gcc-wrap.c](gcc-wrap.c) and put the resulting binary
    into a directory that is in your PATH variable:

      `lwp-download http://www.cprover.org/cprover-manual/gcc-wrap.c`\
      `gcc gcc-wrap.c -o gcc-wrap`\
      `cp gcc-wrap ~/bin/`\

    This assumes that the directory `~/bin` exists and is in your
    PATH variable.

6.  Now change the variable CC in the kernel Makefile as follows:

        CC = ~/bin/gcc-wrap

7.  Now do

        make clean
        make

    This will re-compile the kernel, but this time retaining the
    preprocessed source files.

8.  You can now compile the preprocessed source files with goto-cc as
    follows:

        find ./ -name .tmp_*.i > source-file-list
          for a in `cat source-file-list` ; do
            goto-cc -c $a -o $a.gb
        done

    Note that it is important that the word-size of the kernel
    configuration matches that of goto-cc. Otherwise, compile-time
    assertions will fail, generating the error message "bit field size
    is negative". For a kernel configured for a 64-bit word-width, pass
    the option --64 to goto-cc.

The resulting `.gb` files can be passed to any of the CPROVER tools.

\subsection man_goto-cc-apache goto-cc: Extracting Models from the Apache HTTPD

The [Apache HTTPD](http://httpd.apache.org/) is still the most
frequently used web server. Together with the relevant libraries, it
consists of around 0.4 million lines of C code. In the following, we
show how to extract models from Apache HTTPD 2.4.2.

1.  First of all, we download the sources of Apache HTTPD and two
    supporting libraries and uncompress them:

        lwp-download http://www.mirrorservice.org/sites/ftp.apache.org/apr/apr-1.4.6.tar.bz2
        lwp-download http://www.mirrorservice.org/sites/ftp.apache.org/apr/apr-util-1.4.1.tar.bz2
        lwp-download http://mirror.catn.com/pub/apache/httpd/httpd-2.4.2.tar.bz2
        bunzip2 < apr-1.4.6.tar.bz2 | tar x
        bunzip2 < apr-util-1.4.1.tar.bz2 | tar x
        bunzip2 < httpd-2.4.2.tar.bz2 | tar x

2.  Now compile [gcc-wrap.c](gcc-wrap.c) and put the resulting binary
    into a directory that is in your PATH variable:

        lwp-download http://www.cprover.org/cprover-manual/gcc-wrap.c
        gcc gcc-wrap.c -o gcc-wrap
        cp gcc-wrap ~/bin/

    This assumes that the directory `~/bin` exists and is in your
    PATH variable.

3.  We now build the sources with gcc:

        (cd apr-1.4.6; ./configure; make CC=gcc-wrap)
        (cd apr-util-1.4.1; ./configure --with-apr=../apr-1.4.6 ; make CC=gcc-wrap)
        (cd httpd-2.4.2; ./configure --with-apr=../apr-1.4.6 --with-apr-util=../apr-util-1.4.1 ; make CC=gcc-wrap)

4.  You can now compile the preprocessed source files with goto-cc as
    follows:

        find ./ -name *.i > source-file-list
          for a in `cat source-file-list` ; do
          goto-cc -c $a -o $a.gb
        done

The resulting `.gb` files can be passed to any of the CPROVER tools.
