[CPROVER Manual TOC](../../)

### Assertion Checking

[Assertions](http://en.wikipedia.org/wiki/Assertion_%28computing%29) are
statements within the program that attempt to capture the programmer's
intent. The ANSI C standard defines a header file
[assert.h](http://en.wikipedia.org/wiki/Assert.h), which offers a macro
`assert(cond)`. When executing a statement such as:

```C
assert(p!=NULL);
```

the execution is aborted with an error message if the condition
evaluates to *false*, that is, if `p` is NULL in the example above. The
CPROVER tools can check the validity of the programmer-annotated
assertions statically. Specifically, the CPROVER tools will check that
the assertions hold for *any* nondeterministic choice that the program
can make. The static assertion checks can be disabled using the
`--no-assertions` command line option.

In addition, there is a CPROVER-specific way to specify assertions,
using the built-in function `__CPROVER_assert`:

```C
__CPROVER_assert(p!=NULL, "p is not NULL");
```

The (mandatory) string that is passed as the second argument provides an
informal description of the assertion. It is shown in the list of
properties together with the condition.

The assertion language of the CPROVER tools is identical to the language
used for expressions.  Note that
[nondeterminism](./modeling-nondeterminism.md) can be exploited in order
to check a range of choices.  As an example, the following code fragment
asserts that **all** elements of the array are zero:

```C
int a[100], i;

...

i=nondet_uint();
if(i>=0 && i<100)
  assert(a[i]==0);
```

The nondeterministic choice will guess the element of the array that is
nonzero. The code fragment above is therefore equivalent to:

```C
int a[100], i;

...

for(i=0; i<100; i++)
  assert(a[i]==0);
```

CPROVER also supports writing function pre and postconditions, using
the built-in functions `__CPROVER_precondition` and
`__CPROVER_postcondition`. They can be used to express intent, and at
the moment they are just transformed to assertions in the goto
program. As such, they can be used as simple assertions in
code. However, it is advised to use `__CPROVER_precondition` at the
beginning of a function's body, and `__CPROVER_postcondition` before
the exit points in a function (either the return statements, or the
end of the body if the function returns void). The following is an
example usage:

```C
int foo(int a, int b) {
  __CPROVER_precondition(a >= 0);
  __CPROVER_precondition(b > 0);

  int rval = a / b;

  __CPROVER_postcondition(rval >= 0);
  return rval;
}
```

A future release of CPROVER will support using these pre and
postconditions to create a function contract, which can be used for
modular verification.


Future CPROVER releases will support explicit quantifiers with a syntax
that resembles Spec\#:

```C
__CPROVER_forall { *type identifier* ; *expression* }
__CPROVER_exists { *type identifier* ; *expression* }
```

