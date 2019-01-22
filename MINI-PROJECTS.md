CBMC Mini Projects
==================

The following projects are short, focussed features that give new CBMC
contributors an introduction to one part of the codebase. If you're
interested in contributing to CBMC, feel free to start with any of these
projects!


Task List
---------

### `__CPROVER_print`

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


### Annotation to constrain function pointers

**Task**: implement a CPROVER intrinsic that tells CBMC what function a
function pointer points to.

**Background**: CBMC often doesn't know which function a function
pointer points to. If a function is called through a function pointer,
CBMC currently assumes that *any* function that has the same signature
could be called. This results in a combinatorial explosion of paths when
CBMC is exploring the program. It would be useful to have an annotation
that tells CBMC exactly what function a pointer is expected to point to.


### Generalize loop-unwinding bounds to cover multiple loops

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

```
--unwindset LABEL:BOUND
```

You might like to generalize this so that it looks like

```
--unwindset LABEL<,LABEL2,LABEL3,...>:BOUND
```

which would have the effect that the loops with those labels would all
share a bound.

*Hints*:
- The current member that stores how many times a loop has been unwound
  is `goto_symex_statet::loop_iterations`. Have a look at where this
  member is accessed, and what is done with that value (e.g. read
  through `symex_bmct::should_stop_unwind()` and
  `symex_bmct::loop_unwind_handlert`).

- You may wish to add a map from a *set* of loop names to a loop bound,
  in addition to the current map from single loop names to loop bounds.

- If a loop has an individual bound, and is also part of a set of
  mutually-bound loops, then we should stop unwinding it if *either* of
  those bounds is reached. Good, thoughtful test cases are essential
  here!

Completed
---------


### Add a `--print-internal-representation` switch

*Summary*: This switch should provide more detail than
`--show-goto-functions`, by printing out the `irep` of every program
instruction instead of a concise representation.

*Completed in* PR #991
