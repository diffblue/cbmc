\ingroup module_hidden
\defgroup module_goto-symex Symbolic Execution & Counterexample Production

\author Kareem Khazem

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

The symbolic execution state is maintained by goto_symex_statet. This is
a memory-heavy data structure, so goto_symext creates it on-demand and
lets it go out-of-scope as soon as possible. However, the process of
symbolic execution fills out an additional \ref symbol_tablet
"symbol table" of dynamically-created objects; this symbol table is
needed when solving the equation. This symbol table must thus be
exported out of the state before it is torn down; this is done through
the parameter "`new_symbol_table`" passed as a reference to the various
functions in goto_symext.

The main symbolic execution loop code is goto_symext::symex_step(). This
function case-switches over the type of the instruction that we're
currently executing, and calls various other functions appropriate to
the instruction type, i.e. goto_symext::symex_function_call() if the
current instruction is a function call, goto_symext::symex_goto() if the
current instruction is a goto, etc.

\subsection symex-path Path exploration

By default, CBMC symbolically executes the entire program, building up
an equation representing all instructions, which it then passes to the
solver. Notably, it _merges_ paths that diverge due to a goto
instruction, forming a constraint that represents having taken either of
the two paths; the code for doing this is goto_symext::merge_goto().

CBMC can operate in a different mode when the `--paths` flag is passed
on the command line. This disables path merging; instead, CBMC executes
a single path at a time, calling the solver with the equation
representing that path, then continues to execute other paths.
The 'other paths' that would have been taken when the program branches
are saved onto a workqueue so that CBMC can continue to execute the
current path, and then later retrieve saved paths from the workqueue.
Implementation-wise, \ref bmct passes a worklist to goto_symext in
bmct::do_language_agnostic_bmc(). If path exploration is enabled,
goto_symext will fill up the worklist whenever it encounters a branch,
instead of merging the paths on the branch.  After the initial symbolic
execution (i.e. the first call to bmct::run() in
bmct::do_language_agnostic_bmc()), \ref bmct continues popping the
worklist and executing untaken paths until the worklist empties. Note
that this means that the default model-checking behaviour is a special
case of path exploration: when model-checking, the initial symbolic
execution run does not add any paths to the workqueue but rather merges
all the paths together, so the additional path-exploration loop is
skipped over.

\subsection ssa-renaming SSA renaming levels

In goto-programs, variable names get a prefix to indicate their scope
(like `main::1::%foo` or whatever). At symbolic execution level, variables
also get a _suffix_ because we’re doing single-static assignment. There
are three “levels” of renaming. At Level 2, variables are renamed every
time they are encountered in a function. At Level 1, variables are
renamed every time the functions that contain those variables are
called. At Level 0, variables are renamed every time a new thread
containing those variables are spawned. We can inspect the renamed
variable names with the –show-vcc flag, which prints a string with the
following format: `%%s!%%d@%%d#%%d`. The string field is the variable name,
and the numbers after the !, @, and # are the L0, L1, and L2 suffixes
respectively. The following examples illustrate Level 1 and 2 renaming:

    $ cat l1.c
    int main() {
      int x=7;
      x=8;
      assert(0);
    }
    $ cbmc --show-vcc l1.c
    ...
    {-12} x!0@1#2 == 7
    {-13} x!0@1#3 == 8

That is, the L0 names for both xs are 0; the L1 names for both xs are 1;
but each occurrence of x within main() gets a fresh L2 suffix (2 and 3,
respectively).

    $ cat l2.c
    void foo(){
      int x=7;
      x=8;
      x=9;
    }
    int main(){
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
incremented (from 1 to 2) and the L0 counter is reset (back to 2, after
having been incremented up to 4). The L0 counter then increases every
time we access x as we walk through the function.

---
\section counter-example-production Counter Example Production

In the \ref goto-symex directory.

**Key classes:**
* symex_target_equationt
* prop_convt
* \ref bmct
* fault_localizationt
* counterexample_beautificationt

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
