[CPROVER Manual TOC](../../)

## Understanding Loop Unwinding

### Iteration-based Unwinding

The basic idea of CBMC is to model a program's execution up to a
bounded number of steps. Technically, this is achieved by a process that
essentially amounts to *unwinding loops*. This concept is best
illustrated with a generic example:

```C
int main(int argc, char **argv) {
  while(cond) {
    BODY CODE
  }
}
```

A BMC instance that will find bugs with up to five iterations of the
loop would contain five copies of the loop body, and essentially
corresponds to checking the following loop-free program:

```C
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
```

Note the use of the `if` statement to prevent the execution of the loop
body in the case that the loop ends before five iterations are executed.
The construction above is meant to produce a program that is trace
equivalent with the original programs for those traces that contain up
to five iterations of the loop.

In many cases, CBMC is able to determine automatically an upper bound on
the number of loop iterations. This may even work when the number of
loop unwindings is not constant. Consider the following example:

```C
_Bool f();

int main() {
  for(int i=0; i<100; i++) {
    if(f()) break;
  }
  assert(0);
}
```

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
first use:

    --show-loops

to obtain a list of all loops in the program. Then identify the loops
you need to set a separate bound for, and note their loop ID. Then use:

    --unwindset [T:]L:B

where `L` denotes a loop ID and `B` denotes the bound for that loop in thread T,
if a thread number is included. The initial thread has index 0, and threads are
consecutively numbered in program order of threads being spawned. The
`--unwindset` option can be given multiple times.

As an example, consider a program with two loops in the function main:

    --unwindset main.0:10 --unwindset main.1:20

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

```C
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
```

The unwinding assertions can be verified just like any other generated
assertion. If all of them are proven to hold, the given loop bounds are
sufficient for the program. This establishes a [high-level worst-case
execution time](http://en.wikipedia.org/wiki/Worst-case_execution_time)
(WCET).

In some cases, it is desirable to cut off very deep loops in favor of
code that follows the loop. As an example, consider this program:

```C
int main() {
  for(int i=0; i<10000; i++) {
    BODY CODE
  }
  assert(0);
}
```

In the example above, small values of `--unwind` will prevent that the
assertion is reached. If the code in the loop is considered irrelevant
to the later assertion, use the option

    --partial-loops

This option will allow paths that execute loops only partially, enabling
a counterexample for the assertion above even for small unwinding
bounds. The disadvantage of using this option is that the resulting path
may be spurious, that is, it may not exist in the original program.

### Depth-based Unwinding

The loop-based unwinding bound is not always appropriate. In particular,
it is often difficult to control the size of the generated formula when
using the `--unwind` option. The option:

    --depth nr

specifies an unwinding bound in terms of the number of instructions that
are executed on a given path, irrespective of the number of loop
iterations. Note that CBMC uses the number of instructions in the
control-flow graph as the criterion, not the number of instructions in
the source code.

