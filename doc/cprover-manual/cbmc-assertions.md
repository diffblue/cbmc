[CPROVER Manual TOC](../../)

### Assertion Checking

[Assertions](http://en.wikipedia.org/wiki/Assertion_%28computing%29) are
statements within the program that attempt to capture the programmer's
intent. The ANSI-C standard defines a header file
[assert.h](http://en.wikipedia.org/wiki/Assert.h), which offers a macro
`assert(cond)`. When executing a statement such as

```C
assert(p!=NULL);
```

the execution is aborted with an error message if the condition
evaluates to *false*, i.e., if `p` is NULL in the example above. The
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
used for expressions. Note that \ref man_modelling-nondet
"nondeterminism"
can be exploited in order to check a range of choices. As an example,
the following code fragment asserts that **all** elements of the array
are zero:

```C
int a[100], i;

...

i=nondet_uint();
if(i>=0 && i<100)
  assert(a[i]==0);
```

The nondeterministic choice will guess the element of the array that is
nonzero. The code fragment above is therefore equivalent to

```C
int a[100], i;

...

for(i=0; i<100; i++)
  assert(a[i]==0);
```

Future CPROVER releases will support explicit quantifiers with a syntax
that resembles Spec\#:

```C
__CPROVER_forall { *type identifier* ; *expression* }
__CPROVER_exists { *type identifier* ; *expression* }
```

