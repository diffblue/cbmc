[CPROVER Manual TOC](../../)

## Nondeterminism

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

```C
unsigned short int nondet_ushortint();
```

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

