This file contains various features and project ideas for CBMC. Below
this are the larger feature ideas. Smaller mini project ideas are
further down.

# CBMC Feature and Project Ideas

The following are features that would be good to add to CBMC. They are
listed here to gather information on them and also as a starting point
for contributors who are interested in undertaking a more comprehensive
project.

## Refinement-Based Slicing

**Task**: Implement refinement-based slicing to improve the slicing
of CBMC.

**Background**:
Some patches have been considered for this, but there is not yet
evidence of performance improvement. See
https://github.com/diffblue/cbmc/issues/28

## Refinement-based reduction of partial order constraints

**Task**: Implement refinement-based reduction of partial order
constraints.

**Background**:
Some patches have been considered for this, but there needs to also be
work on the performance. See
https://github.com/diffblue/cbmc/issues/29


## Advanced goto-diff

**Task**: Improve the goto-diff utility to have both syntactic and
semantic diff options for goto programs.

**Background**: The current `goto-diff` program performs only syntatic
diff of goto programs. Extensions to also consider semantic differences
would be desirable. It would be nice to include:
* deltacheck's change impact analysis
* cemc equivalence checker

See also https://github.com/diffblue/cbmc/issues/40

## Function Summaries

**Task**: Create function summaries that simplify analysis. The main
goals of the function summaries are:
* context insensitivity (there is one summary applicable in any
context the function is called from)
* transitive closure (effects of all callees are captured in summaries
of the root caller function)
* generalised interface (suitable for many different concrete
summary-computing algorithms)
* language independent (should work for Java, C, C++, ...)

This also has links to other projects (albeit some may be out of date
at this stage):
* test_gen (our summaries should fit to needs of this tests generation
task)
* 2ls (their summaries should also be expressible in our summaries)
* path-symex (summaries must also be usable for path-based symbolic
execution)

There are also complexities related to over/under-approximation
for the function summaries. For more details see
https://github.com/diffblue/cbmc/issues/218


## --cover array

**Task**: Extend the `--cover` option to add coverage goals for each
possible entry of fixed size arrays. For more details see
https://github.com/diffblue/cbmc/issues/265


## Connecting Producers and Consumers of Knowledge about Termination

There is very limited knowledge about loop termination conditions
and this could be improved. For example, the slicing could be
improved with knoweldge regarding loop termination so that
irrelevant loops can be more effectively sliced. Similarly, in
goto-analyze assertions can only be false if reachable, adding
termination can give crude reachability analysis.

The overall approach could be to have for each loop and/or
function information: `TERMINATE`, `NON_TERMINATE`, or
`UNKNOWN_TERMINATION`.

Further details on possible implementations and discussion
can be found here
https://github.com/diffblue/cbmc/issues/618

# CBMC Mini Project Ideas

The following projects are short, focussed features that give new CBMC
contributors an introduction to one part of the codebase. If you're
interested in contributing to CBMC, feel free to start with any of these
projects!

## `__CPROVER_print`

**Task**: Implement a CPROVER intrinsic that assigns an expression to a
dummy value, to help with debugging and tracing.

**Background**:
Inserting `printf("value of expr: %d\n", expr);` is a common debugging
and tracing technique. The CBMC equivalent is to assign an expression to
a temporary variable and run `cbmc --trace`:

```c
$ cat foo.c
#define __CPROVER_print(var) { int value_of_##var = (int) var; }

void foo(int x)
{
  __CPROVER_print(x);
  assert(0);  // Make CBMC halt its exploration and dump a trace up to
              // this point
}

int main()
{
  foo(3);
}
```

This has several limitations (we need different variants of the macro
for pointers, etc). It would be great to have `__CPROVER_print` as a
CPROVER intrinsic, so that users don't need to do the awkward define or
manual ghost assignment in their code.

**Hints**: Figure out how `__CPROVER_assume` and `__CPROVER_assert` work.
Then figure out how to add new instructions into a goto-program.

## Annotation to constrain function pointers

**Task**: implement a CPROVER intrinsic that tells CBMC what function a
function pointer points to.

**Background**: CBMC often doesn't know which function a function
pointer points to. If a function is called through a function pointer,
CBMC currently assumes that *any* function that has the same signature
could be called. This results in a combinatorial explosion of paths when
CBMC is exploring the program. It would be useful to have an annotation
that tells CBMC exactly what function a pointer is expected to point to.

## Generalize loop-unwinding bounds to cover multiple loops

**Task**: allow users to specify a *combined* bound for the sum of
several loop counters.

**Background**: consider a program that uses several nested while-loops
to move a pointer through a buffer. Each of the nested loops may advance
the pointer. We want to ensure that the pointer doesn't overflow the
buffer.

Unfortunately, if we specify the buffer size `S` as the loop bound for
those three loops, we can still overflow the buffer because all three of
the loops can move the pointer forward `S` times. What we need is to
specify that the *combined* loop bound for the three loops is `S`.

The current syntax for the `--unwindset` switch is

```sh
--unwindset LABEL:BOUND
```

You might like to generalize this so that it looks like

```sh
--unwindset LABEL<,LABEL2,LABEL3,...>:BOUND
```

which would have the effect that the loops with those labels would all
share a bound.

*Hints*:

* The current member that stores how many times a loop has been unwound
  is `goto_symex_statet::loop_iterations`. Have a look at where this
  member is accessed, and what is done with that value (e.g. read
  through `symex_bmct::should_stop_unwind()` and
  `symex_bmct::loop_unwind_handlert`).

* You may wish to add a map from a *set* of loop names to a loop bound,
  in addition to the current map from single loop names to loop bounds.

* If a loop has an individual bound, and is also part of a set of
  mutually-bound loops, then we should stop unwinding it if *either* of
  those bounds is reached. Good, thoughtful test cases are essential
  here!

## Instrumentation to Check Pointer Alignment

Some architectures only allow load instructions / pointer dereferencing when the
address is a multiple of the word length (i.e. 4 bytes or 8 bytes). This project
would add a new instrumentation option for `cbmc` and `goto-instrument` that checks
each pointer before dereference and makes sure it's correctly aligned.

This is a good way to get into `goto_check` and how instrumentation of asserts
works.

## Command line options to SAT solvers

There are options for which SMT solver to run and there are ways of building with
multiple SAT solvers but no command line options to pick a SAT solver. It would be
nice if there were.

## Combine Uninitialized Variables Analysis with Alias Analysis

`goto-instrument` features an instrumentation to track cases of use-before-define,
i.e. reading of uninitialised variables. At present, the analysis does not take
into account aliasing information. As such, the following code will yield a spurious
counterexample:

``` C
int main()
{
  int x;
  int *ptr;
  ptr=&x;
  *ptr=42;
  if(x < 42)
    return 1;
  return 0;
}
```

This should be pretty straight-forward to do with `goto-analyzer --vsd` and might even
be a good intro to that code.

## Make SAMATE Tests Work

Read [this paper](https://www.sciencedirect.com/science/article/abs/pii/S0950584913000384) and
make the tests mentioned in there work.

## Error Explanation

Re-implement the algorithm described in [this paper](http://www.kroening.com/papers/STTT-error-explanation-2005.pdf)

## LTL

Build an instrumenter in `goto-instrument` for checking LTL (or even CTL) properties
on C code. E.g look at [this paper](https://www.umsec.umn.edu/publications/Partial-Translation-Verification-Untrusted-Code)

Please get in touch with Michael Tautschnig, who has done very similar work in FShell.

## Test SMT Back Ends

CBMC allows to choose among a selection of SMT solvers to use as solving back end.
As these tools evolve, CBMC's code for running them may need a fresh look from time
to time. After a first round of manual experiments, these tests should become part
of the routine build process on `dkr-build`. (Michael Tautschnig knows how to do this.)

## Improved Interpreter

CProver has an interpreter for goto programs but it could be improved, for example adding
support for dynamic analysis, calls to external functions and possibly even mixed concrete
and symbolic execution. It would also be good to be able to interpret traces found by BMC
to catch mismatches / bugs between the logical model and the bit blasting models. This
would also be useful for more advanced CEGAR like techniques (also see below).

## "KLEE-PROVER"

Alter the CBMC symbolic execution engine to create a dynamic symbolic execution tool
similar to [KLEE](https://klee.github.io/). Possible features include:

* Distributed and incremental support using the caching scheme here
* A feature to run BMC as you go to explore the traces 'around' the execution traces
* Use path exploration as the witness generation part of an ACDL process.
* Perform precondition inference, possibly using ACDL.

## Interact with GDB

GDB implements a client-server protocol with a GDB instance acting as a server and the
GUI as a client. (The documentation for that protocol may be found [here](http://www.sourceware.org/gdb/current/onlinedocs/gdb/GDB_002fMI.html).)
By implementing this protocol in various places within CProver, there are various
things that could be achieved.

To do some of these will require working out which functions are non-deterministic models
of real functions and accounting for this. This would also be necessary for some of the
preceeding ideas.

### Trace as a GDB server

Implement a GDB server that uses a trace to 'execute' the program. This allows any GUI
debugger that can talk to GDB to be used to graphically explore the trace. Particularly
valuable for concurrent programs in which just reading the trace could be very hard.

An implementation of that is in the trace debugger here: https://github.com/diffblue/eclipse-cbmc

Handling the SV-COMP counter-example format (ask Michael) would probably make this tool
a lot more widely usable.

### Trace as a GDB client

Conversely, implement a GDB client that uses the trace to control a debugger. If
connected to a 'real' GDB then this would allow the debugger to be set to the position
that shows the error. In the case of parallel programs this avoids the need to create
custom schedulers, etc. and over-all it is a much better interface – rather than
generate a trace, CProver simply gives you the debugger in the state that triggers
the problem.

One option would be to convert the trace to a GDB script but this misses some of
the value as it would be possible to query they GDB server as the program runs to
check that values really are assigned correctly. This will catch the first point
at which the model and the real system diverge and allows checked 'resimulation'
of the traces on a 'real' platform. If the goto-binary contains the ELF binary
then this could be used directly.

### Interpreter as a GDB server

An enabling tech, this would allow us to run the interpreter as a debugger back
end. Combine with the trace as a GDB client, this would allow resimulation of
traces, which would be useful for catching encoding bugs in CProver and ideally
should be run after the decode from the solver all of the time.

Michael has a partial implementation of this. (?)

### Recording GDB server

Acts as a GDB server and passes commands back to another GDB server to actually
execute. Records the state changes and locations visited. This allows a test case
to be 'run' and the trace / conditions on the trace to be collected and (after
generalisation) be used for test case driven analysis / test case generalisation
/ something “concolic” like.

### Differential GDB server

Acts as a GDB server and then connects (as a client) to one or more GDB servers.
Commands are executed on all of these and then the state / position compared
(much of the infrastructure of the previous idea could be used). Divergences of
behaviour can then be found, particularly root causes can be identified by the
first divergence. This may not be CProver specific but can likely be used for
various projects and ideas above.

### "Concolic" GDB client

An interactive component that runs a program via a GDB server and query / interact
with it. This would be useful for building a “concolic” tool, especially for running
library functions that are not defined.

## Other ideas

Valgrind and the Linux kernel both have GDB servers - what could we do with these?

### Static Detection of Data Races

It would be good to have a tool that checks for data races in a similar fashion to
DRD / Helgrind. The current pointer analysis can over approximate shared variables,
so possibly some combination of this, trace generation, DRD / Helgrind and then
refinement of which traces to pick? Perhaps this is even something ACDL like?

### CORAL / Q

Build something similar to the Q tool in SLAM. (?)

### k-liveness

Implement [k-liveness](http://www.cs.utexas.edu/~hunt/FMCAD/FMCAD12/013.pdf)
for software-liveness checking.

### Known Bugs on the Web

Turn the list of `KNOWNBUG`S from the CBMC regressions into a list of open issues
in the CBMC repository issue tracker (https://github.com/diffblue/cbmc/issues).

If you do this, make sure you target either the`develop` branch or the latest
CBMC release.

### Coding Standards Checker

Build instrumenters for various coding standards, e.g. AutoSar, [MISRA-C](https://en.wikipedia.org/wiki/MISRA_C),
CERT-C, [HIC++](https://www.perforce.com/resources/qac/high-integrity-cpp-coding-standard),
etc.

### Front-End Testing

Run the regressions mentioned [here](https://github.com/kframework/c-semantics/tree/master/tests)
and the [GCC C Torture tests](https://gcc.gnu.org/onlinedocs/gccint/C-Tests.html)
with `goto-cc` and a `goto-program` interpreter.

### Unspecified C Behaviours

Build instrumentation to check for unspecified behaviours in C, as per Section J.2
(and maybe also J.3) of the C standard. Some of them may be possible to handle
entirely in the front-end (for example, catching `x = x++` as modifying a variable
twice between sequence points could be done in side effect removal in ansi-c), while
others may be best to be instrumentation (for example handling the unspecified nature
of the order of evaluation of function arguments).

For more information, talk to Michael Tautschnig for this item.

### Reporting Software Errors with CWE Information

The [Common Weakness Enumeration project](http://cwe.mitre.org/) seeks to classify
software weaknesses and errors in a common dictionary. Reporting CWE information together
with failed assertions, such as [Free of Pointer not at Start of Buffer](http://cwe.mitre.org/data/definitions/761.html),
would help both users of the tools as well as industrial partners. In the first instance,
errors already caught by present instrumentation should be augmented with additional
information. In a second step, instrumentation for other problems listed in the CWE
database should be developed.

### Machine Learn Refinement settings

The refinement option enables a tactic of under and over approximation to try to
solve the generated formulae more quickly. There are a large number of possible
options – which operations to approximate, how much to under or over approximate
them, how much to add back if this doesn't work, etc. Rather than trying to manually
pick the best strategy from these, it would be good to machine learn them.

### Cluster CBMC

Most users of CBMC have access to multi-core machines; many have clusters available.
There are a number of different approaches and a number of different levels at which
the task could be parallelised; per assertion, portfolio approaches of different
back-ends, parallel solvers, etc. It would be good to be able to exploit these.
The caching approach suggested under “KLEE-PROVER” might be an easy route to
implementing this.

### x86 to Goto

Look at various efforts to model x86 assembler, e.g., Andrew Kennedy,
“Formalizing .EXEs, .DLLs, and all that”, Gang Tan, “Reusable tools for formal
modeling of machine code”, and check whether this can turn into a translator
from x86 to goto binary.

Also look at Google's Native Client, and talk to Matt, who has tried Valgrind.

Furthermore, talk to Michael, who has got a student who made some progress
on this.

And maybe have a read of Automated synthesis of symbolic instruction encodings
from I/O samples.

### Branch Prediction

Implement branch prediction algorithms in path-symex.

### GCC Torture Tests

GCC has a set of 'torture tests' which are intended to stress test and find bugs in their
parser and front-end. It would be good to run these through goto-cc / add them to the
nightly testing and fix any bugs that arise. (Possible overlap with “Front-End Testing”
above.). The same is probably also true for other compiler fuzzing tools.

### Compiler loop optimisations for BMC

Try out some of the compiler loop optimisations (hoisting invariant code,
fusing sequential independent loops, etc.) and see if they improve BMC,
K-Induction or loop acceleration. These should be possible to implement in
goto-instrument.

### Handling restrict in a smart way

C99 adds the `restrict` keyword to mark unaliased pointers. This can be discarded by
the compiler and thus has no semantics, it is only an annotation. However, there are
a number of thing we could do with:

1. Insert checks in calling functions to make sure that the pointers really are unaliased.
2. Add an instrumentation pass that adds assumptions that restricted pointers are not
   aliased. This may imporve the quality of counter-examples (although at the cost of
   potentially missing some bugs, although not if combined with the previous technique).

### C++ Exceptions

C++ has annotations for what exceptions a function can throw. It would be good to
be able to check / generate / minimise these and it should be possible to do this
with a reasonably simple abstract domain. The CVC4 project would be interested in
using this if it exists.

An old prototype of something similar is here: https://github.com/peterschrammel/cbmc/commits/progres-exceptions

### Java Memory Model

CBMC's Java front-end is currently in development and will support the full Java
bytecode instruction set soon. Beyond that, it would be great to support some more
advanced aspects of the Java programming language semantics, such as the Java Memory
Model. This will include adding models for a subset of the Java concurrency packages
in the Java Runtime Library.
