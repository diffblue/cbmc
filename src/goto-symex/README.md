\ingroup module_hidden
\defgroup goto-symex goto-symex

# Folder goto-symex

\author Kareem Khazem, Martin Brain

This directory contains a symbolic evaluation system for goto-programs.
This takes a goto-program and translates it to an equation system by
traversing the program, branching and merging and unwinding loops and recursion
as needed.

The output of symbolic execution is a system of equations, asserations and
assumptions; an object of type `symex_target_equationt`, containing a list of
`symex_target_equationt::SSA_stept`, each of which are equalities between
`exprt` expressions. This list is constructed incrementally as the symbolic
execution engine walks through the goto-program using the `symex_targett`
interface. This interface (implemented by `symex_target_equationt`) exposes
functions that append SSA steps into the aforementioned list while transforming
expressions into Static Single Assignment (SSA) form. For more details on this
process see `symex_target_equation.h`, for an overview of SSA see \ref
static-single-assignment.

At a later stage, BMC will convert the generated SSA steps into an
equation that can be passed to the solver.

---
\section symbolic-execution Symbolic Execution

In the \ref goto-symex directory.

**Key classes:**
* goto_symex_statet
* goto_symext

\dot
digraph G {
	node [shape=box];
	rankdir="LR";
	1 [shape=none, label=""];
	2 [label="goto conversion"];
	3 [shape=none, label=""];
	1 -> 2 [label="goto-programs, goto-functions, symbol table"];
	2 -> 3 [label="equations"];
}
\enddot

\subsection symex-overview Overview

The \ref bmct class gets a reference to an \ref symex_target_equationt
"equation" (initially, an empty list of \ref symex_target_equationt::SSA_stept
"single-static assignment steps") and a goto-program from the frontend.
The \ref bmct creates a goto_symext to symbolically execute the
goto-program, thereby filling the equation, which can then be passed
along to the SAT solver.

The class \ref goto_symext holds the global state of the symbol executor, while
\ref goto_symex_statet holds the program state at a particular point in
symbolic execution. In straight-line code a single \ref goto_symex_statet is
maintained, being transformed by each instruction in turn, but these state
objects are cloned and merged at control-flow forks and joins respectively.
\ref goto_symex_statet contains an instance of \ref value_sett, used to track
what objects pointers may refer to, and a constant propagator domain used to
try to simplify assignments and (more usefully) resolve branch instructions.

This is a memory-heavy data structure, so goto_symext creates it on-demand and
lets it go out-of-scope as soon as possible.

The process of
symbolic execution generates an additional \ref symbol_tablet
"symbol table" of dynamically-created objects; this symbol table is
needed when solving the equation. This symbol table must thus be
exported out of the state before it is torn down; this is done through
the parameter "`new_symbol_table`" passed as a reference to the various
functions in goto_symext.

The main symbolic execution loop code is \ref goto_symext::symex_step. This
function case-switches over the type of the instruction that we're
currently executing, and calls various other functions appropriate to
the instruction type, i.e. goto_symext::symex_function_call() if the
current instruction is a function call, goto_symext::symex_goto() if the
current instruction is a goto, etc.

\subsection symex-loop-and-recursion-unwinding Loop and recursion unwinding

Each backwards goto and recursive call has a separate counter
(handled by \ref cbmc or another driver program, see the `--unwind` and
`--unwind-set` options). The symbolic execution includes constant
folding so loops that have a constant / bounded number of iterations will often
be handled completely (assuming the unwinding limit is sufficient).
When an unwind or recursion limit is reached, an assertion can be added to
explicitly show when analysis is incomplete.

\subsection goto-symext-clean-expr goto_symext::clean_expr

Before any expression is incorporated into the output equation set it is passed
through \ref goto_symext::clean_expr and thus \ref goto_symext::dereference,
whose primary purpose is to remove dereference operations. It achieves this
using the \ref value_sett stored in \ref goto_symex_statet, replacing `*x` with
a construct such as
`x == &candidate1 ? candidate1 : x == &candidate2 ? candidate2 : x$object`

Note the `x$object` fallback candidate, which is known as a *failed symbol* or
*failed object*, and represents the unknown object pointed to by `x` when
neither of the candidates (`candidate1` and `candidate2` here) matched as
expected. This is of course unsound, since `x$object` and `y$object` are always
distinct, even if `x` and `y` might actually alias, but at least it ensures
writes to and subsequent reads from `x` are related.

\ref goto_symext::dereference function also passes its argument to
\ref goto_symex_statet::rename, which is responsible for both SSA
renaming symbols and for applying constant propagation where possible. Renaming
is also performed elsewhere without calling \ref goto_symext::dereference when
an expression is already known to be pointer-free.

\subsection symex-path Path exploration

By default, CBMC symbolically executes the entire program, building up
an equation representing all instructions, which it then passes to the
solver. Notably, it _merges_ paths that diverge due to a goto
instruction, forming a constraint that represents having taken either of
the two paths; the code for doing this is \ref goto_symext::merge_goto.

Goto-symex can operate in a different mode when the `--paths` flag is passed
in the \ref optionst object passed to its constructor (\ref cbmc passes this
from the corresponding command-line option).
This disables path merging; instead, symex executes
a single path at a time, returning each one to its caller, which in the case of
cbmc then calls its solver with the equation
representing that path, then continues to execute other paths.
The 'other paths' that would have been taken when the program branches
are saved onto a workqueue so that the driver program can continue to execute
the current path, and then later retrieve saved paths from the workqueue.
Implementation-wise, \ref bmct passes a worklist to goto_symext in
\ref bmct::do_language_agnostic_bmc. If path exploration is enabled,
goto_symext will fill up the worklist whenever it encounters a branch,
instead of merging the paths on the branch.  After the initial symbolic
execution (i.e. the first call to \ref bmct::run in
\ref bmct::do_language_agnostic_bmc), \ref bmct continues popping the
worklist and executing untaken paths until the worklist empties. Note
that this means that the default model-checking behaviour is a special
case of path exploration: when model-checking, the initial symbolic
execution run does not add any paths to the workqueue but rather merges
all the paths together, so the additional path-exploration loop is
skipped over.

---
\section static-single-assignment Static Single Assignment (SSA) Form

**Key classes:**
* \ref symex_targett
* \ref symex_target_equationt

*Static Single Assignment (SSA)* form is an intermediate
representation that satisfies the following properties:

1. Every variable is *assigned exactly once*.
2. Every variable must be *defined* before use.

In-order to convert a goto-program to SSA form all variables are
indexed (renamed) through the addition of a _suffix_.

There are three “levels” of indexing:

**Level 2 (L2):** variables are indexed every time they are
encountered in a function.

**Level 1 (L1):** variables are indexed every time the functions that
contain those variables are called.

**Level 0 (L0):** variables are indexed every time a new thread
containing those variables are spawned.

We can inspect the indexed variable names with the **--show-vcc** or
**--program-only** flags. Variables in SSA form are printed in the
following format: `%%s!%%d@%%d#%%d`. Where the string field is the
variable name, and the numbers after the !, @, and # are the L0, L1,
and L2 suffixes respectively.

> Note: **--program-only** prints all the SSA steps in-order. In
> contrast, **--show-vcc** will for each assertion print the SSA steps
> (assumes, assignments and constraints only) that synthetically
> precede the assertion. In the presence of multiple threads it will
> also print SSA steps that succeed the assertion.

\subsection L1-L2 Level 1 and level 2 indexing

The following examples illustrate Level 1 and 2 indexing.

    $ cat l1.c
    int main()
    {
      int x=7;
      x=8;
      assert(0);
    }

    $ cbmc --show-vcc l1.c
    ...
    {-12} x!0@1#2 == 7
    {-13} x!0@1#3 == 8

That is, the L0 names for both x's are 0; the L1 names for both x's
are 1; but each occurrence of x within main() gets a fresh L2 suffix
(2 and 3, respectively).

    $ cat l2.c
    void foo()
    {
      int x=7;
      x=8;
      x=9;
    }
    int main()
    {
      foo();
      foo();
      assert(0);
    }

    $ cbmc --show-vcc l2.c
    ...
    {-12} x!0@1#2 == 7
    {-13} x!0@1#3 == 8
    {-14} x!0@1#4 == 9
    {-15} x!0@2#2 == 7
    {-16} x!0@2#3 == 8
    {-17} x!0@2#4 == 9

That is, every time we enter function foo, the L1 counter of x is
incremented (from 1 to 2) and the L2 counter is reset (back to 2,
after having been incremented up to 4). The L2 counter then increases
every time we access x as we walk through the function.

\subsection L0 Level 0 indexing (threads only)

TODO: describe and give a concrete example

\subsection PL Relevant Primary Literature

Thread indexing is based on the following paper:

> Lee, J., Midkiff, S.P. and Padua, D.A., 1997, August. Concurrent
> static single assignment form and constant propagation for
> explicitly parallel programs. In International Workshop on Languages
> and Compilers for Parallel Computing (pp. 114-130). Springer,
> Berlin, Heidelberg.

Seminal paper on SSA:

> Rosen, B.K., Wegman, M.N. and Zadeck, F.K., 1988, January. Global
> value numbers and redundant computations. In Proceedings of the 15th
> ACM SIGPLAN-SIGACT symposium on Principles of programming languages
> (pp. 12-27). ACM.

---
\section counter-example-production Counter Example Production

In the \ref goto-symex directory.

**Key classes:**
* \ref symex_target_equationt
* \ref prop_convt
* \ref bmct
* \ref fault_localizationt
* \ref counterexample_beautificationt

\dot
digraph G {
  node [shape=box];
  rankdir="LR";
  1 [shape=none, label=""];
  2 [label="goto conversion"];
  3 [shape=none, label=""];
  1 -> 2 [label="solutions"];
  2 -> 3 [label="counter-examples"];
}
\enddot
