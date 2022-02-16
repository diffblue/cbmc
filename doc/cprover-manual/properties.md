## Automatically Generating Properties

### What is a "Property"?

We have mentioned *properties* several times so far, but we never
explained *what* kind of properties CBMC can verify. We cover
this topic in more detail in this section.

CBMC uses
[assertions](http://en.wikipedia.org/wiki/Assertion_(computing)) to
specify program properties. Assertions are properties of the state of
the program when the program reaches a particular program location.
Assertions are often written by the programmer using the `assert`
macro.

In addition to the assertions written by the programmer, assertions for
specific properties can also be generated automatically by CBMC, often
relieving the programmer from expressing properties that should hold in any
well-behaved program.

CBMC comes with an assertion generator, which performs a conservative [static
analysis](http://en.wikipedia.org/wiki/Static_code_analysis) to determine
program locations that potentially contain a bug.  Due to the imprecision of
the static analysis, it is important to emphasize that these generated
assertions are only *potential* bugs, and that the Model Checker first needs
to confirm that they are indeed genuine bugs.

The assertion generator can generate assertions for the verification of
the following properties:

-   **Buffer overflows.** For each array access, check whether the upper
    and lower bounds are violated.

-   **Pointer safety.** Search for `NULL`-pointer dereferences or
    dereferences of other invalid pointers.

-   **Memory leaks.** Check whether the program constructs dynamically
    allocated data structures that are subsequently inaccessible.

-   **Division by zero.** Check whether there is a division by zero in
    the program.

-   **Not-a-Number.** Check whether floating-point computation may
    result in [NaNs](http://en.wikipedia.org/wiki/NaN).

-   **Arithmetic overflow.** Check whether a numerical overflow occurs
    during an arithmetic operation.

-   **Undefined shifts.** Check for shifts with excessive distance.

We won't explain the properties in detail. Most of them
relate to behaviors that are left undefined by the respective language
semantics. For a discussion on why these behaviors are usually very
undesirable, read [this](http://blog.regehr.org/archives/213) blog post
by John Regehr.

All the properties described above are *reachability* properties. They
are always of the form

"*Is there a path through the program such that some property is
violated?*"

The counterexamples to such properties are always program paths. Users
of the Eclipse plugin can step through these counterexamples in a way
that is similar to debugging programs. The installation of this plugin
is explained [here](http://www.cprover.org/eclipse-plugin/).

### Using goto-instrument

The goto-instrument static analyzer operates on goto-binaries, which is
a binary representation of control-flow graphs. The goto-binary is
extracted from program source code using goto-cc, which is explained
[here](../goto-cc/). Given a goto-program, goto-instrument operates
as follows:

1.  A goto-binary is read in.
2.  The specified static analyses are performed.
3.  Any potential bugs found are transformed into corresponding
    assertions, and are added into the program.
4.  A new goto-binary (with assertions) is written to disc.

As an example, we begin with small C program we call `expr.c` (taken
from [here](http://www.spinroot.com/uno/)):

```C
int *ptr;

int main(void) {
  if (ptr)
    *ptr = 0;
  if (!ptr)
    *ptr = 1;
}
```

The program contains an obvious NULL-pointer dereference. We first
compile the example program with goto-cc and then instrument the
resulting goto-binary with pointer checks.

```
goto-cc expr.c -o in.gb   goto-instrument in.gb out.gb --pointer-check
```

We can now get a list of the assertions that have been generated:

```
goto-instrument out.gb --show-properties
```

Using CBMC on `out.gb`, we can obtain a counterexample
trace for the NULL-pointer dereference:

```
cbmc out.gb
```

The goto-instrument program supports these checks:

|Flag                          |  Check                                               |
|------------------------------|------------------------------------------------------|
| `--no-assertions`            |  ignore user assertions                              |
| `--bounds-check`             |  add array bounds checks                             |
| `--div-by-zero-check`        |  add division by zero checks                         |
| `--pointer-check`            |  add pointer checks                                  |
| `--pointer-primitive-check`  |  add pointer primitive checks                        |
| `--signed-overflow-check`    |  add arithmetic over- and underflow checks           |
| `--unsigned-overflow-check`  |  add arithmetic over- and underflow checks           |
| `--undefined-shift-check`    |  add range checks for shift distances                |
| `--nan-check`                |  add floating-point NaN checks                       |
| `--uninitialized-check`      |  add checks for uninitialized locals (experimental)  |
| `--error-label label`        |  check that given label is unreachable               |

As all of these checks apply across the entire input program, we may wish to
disable or enable them for selected statements in the program. 
For example, unsigned overflows can be expected and acceptable in certain 
instructions even when elsewhere we do not expect them. 
As of version 5.12, CBMC supports selectively disabling or enabling
automatically generated properties using pragmas.


CPROVER pragmas are handled using a stack:
- `#pragma CPROVER check push` pushes a new level on the pragma stack
- `#pragma CPROVER check disable "<name_of_check>"` adds a disable pragma
  at the top of the stack
- `#pragma CPROVER check enable "<name_of_check>"` adds a enable pragma
  at the top of the stack
- an `enable` or `disable` pragma for a given check present at the top level
  of the stack shadows other pragmas for the same in lower levels of the stack
- adding both `enable` and `disable` pragmas for a same check in a same level
  of the stack creates a PARSING_ERROR.
- `#pragma CPROVER check pop` pops a level in the stack and restores the state
  of pragmas at the sub level

For example, for unsigned overflow checks, use

```
unsigned foo(unsigned x)
{
#pragma CPROVER check push
#pragma CPROVER check enable "unsigned-overflow"
  // unsigned overflow check apply here
  x = x + 1;
#pragma CPROVER check pop
  // unsigned overflow checks do not apply here
  x = x + 2;
```

```
unsigned foo(unsigned x)
{
#pragma CPROVER check push
#pragma CPROVER check enable "unsigned-overflow"
#pragma CPROVER check enable "signed-overflow"
  // unsigned and signed overflow check apply here
  x = x + 1;
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
  // only signed overflow check apply here
  x = x + 2;
#pragma CPROVER check pop
  // unsigned and signed overflow check apply here
  x = x + 3;
#pragma CPROVER check pop
  // unsigned overflow checks do not apply here
  x = x + 2;
```

```
unsigned foo(unsigned x)
{
#pragma CPROVER check push
#pragma CPROVER check enable "unsigned-overflow"
#pragma CPROVER check enable "signed-overflow"
  // unsigned and signed overflow check apply here
  x = x + 1;
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#pragma CPROVER check enable "unsigned-overflow"
  // PARSING_ERROR Found enable and disable pragmas for unsigned-overflow-check
  x = x + 2;
#pragma CPROVER check pop
  x = x + 3;
#pragma CPROVER check pop
  x = x + 2;
```

#### Flag --nan-check limitations

Please note that `--nan-check` flag is adding not-a-number checks only for
generation of NaN value. Current implementation of `--nan-check` flag is not
providing checks for propagation of NaN values. Generating assertions on type
casting or structure/union member access is unsupported and such operation
will not be examined.

For example:

```
float f = 0.0/0.0; // will generate NaN - CBMC will add assertion
float g = NAN+0.0; // propagation of NaN value - no assertion generated
```

#### Generating function bodies

Sometimes implementations for called functions are not available in the goto
program, or it is desirable to replace bodies of functions with certain
predetermined stubs (for example to confirm that these functions are never
called, or to indicate that these functions will never return). For this purpose
goto-instrument provides the `--generate-function-body` option, that takes a
regular expression (in [ECMAScript
syntax](http://en.cppreference.com/w/cpp/regex/ecmascript)) that describes the names of
the functions to generate. Note that this will only generate bodies for
functions that do not already have one; If one wishes to replace the body of a
function with an existing definition, the `--remove-function-body` option can be
used to remove the body of the function prior to generating a new one.

The shape of the stub itself can be chosen with the
`--generate-function-body-options` parameter, which can take these values:

| Option                      | Result                                                      |
|-----------------------------|-------------------------------------------------------------|
| `nondet-return`             | Do nothing and return a nondet result (this is the default) |
| `assert-false`              | Make the body contain an assert(false)                      |
| `assume-false`              | Make the body contain an assume(false)                      |
| `assert-false-assume-false` | Combines assert-false and assume-false                      |
| `havoc`                     | Set the contents of parameters and globals to nondet        |

The various combinations of assert-false and assume-false can be used to
indicate that functions shouldn't be called, that they will never return or
both.

Example: We have a program like this:

```C
// error_example.c
#include <stdlib.h>

void api_error(void);
void internal_error(void);

int main(void)
{
  int arr[10] = {1,2,3,4,5, 6, 7, 8, 9, 10};
  int sum = 0;
  for(int i = 1; i < 10; ++i)
  {
    sum += arr[i];
  }
  if(sum != 55)
  {
    // we made a mistake when calculating the sum
    internal_error();
  }
  if(rand() < 0)
  {
    // we think this cannot happen
    api_error();
  }
  return 0;
}
```

Now, we can compile the program and detect that the error functions are indeed
called by invoking these commands:

```
goto-cc error_example.c -o error_example.gb
# Replace all functions ending with _error
# (Excluding those starting with __)
# With ones that have an assert(false) body
goto-instrument error_example.gb error_example_replaced.gb \
  --generate-function-body '(?!__).*_error' \
  --generate-function-body-options assert-false
cbmc error_example_replaced.gb
```

This generates the following output:

```
** Results:
error_example.c function api_error
[api_error.assertion.1] line 4 assertion false: FAILURE

error_example.c function internal_error
[internal_error.assertion.1] line 5 assertion false: FAILURE

** 2 of 2 failed (2 iterations)
VERIFICATION FAILED
```

Without the instrumentation step we would have seen
"VERIFICATION SUCCESSFUL".

The havoc option takes further parameters `globals` and `params` with this
syntax: `havoc[,globals:<regex>][,params:<regex>]` (where the square brackets
indicate an optional part). The regular expressions have the same format as the
those for the `--generate-function-body` option and indicate which globals and
function parameters should be set to nondet. All regular expressions require
exact matches (i.e. the regular expression `a|b` will match 'a' and 'b' but not
'adrian' or 'bertha').

Example: With a C program like this

```C
struct Complex {
  double real;
  double imag;
};

struct Complex AGlobalComplex;
int do_something_with_complex(struct Complex *complex);
```

And the command line

```
goto-instrument in.gb out.gb
  --generate-function-body do_something_with_complex
  --generate-function-body-options
    'havoc,params:.*,globals:AGlobalComplex'
```

The goto code equivalent of the following will be generated:

```C
int do_something_with_complex(struct Complex *complex)
{
  if(complex)
  {
    complex->real = nondet_double();
    complex->imag = nondet_double();
  }
  AGlobalComplex.real = nondet_double();
  AGlobalComplex.imag = nondet_double();
  return nondet_int();
}
```

A note on limitations: Because only static information is used for code
generation, arrays of unknown size and pointers will not be affected by this.
Which means that for code like this:

```C
struct Node {
  int val;
  struct Node *next;
};

void do_something_with_node(struct Node *node);
```

Code like this will be generated:

```C
void do_something_with_node(struct Node *node)
{
   if(node)
   {
     node->val = nondet_int();
     node->next = nondet_0();
   }
}
```

Note that no attempt to follow the `next` pointer is made. If an array of
unknown (or 0) size is encountered, a diagnostic is emitted and the array is not
further examined.

Some care must be taken when choosing the regular expressions for globals and
functions. Names starting with `__` are reserved for internal purposes; For
example, replacing functions or setting global variables with the `__CPROVER`
prefix might make analysis impossible. To avoid doing this by accident, negative
lookahead can be used. For example, `(?!__).*` matches all names not starting
with `__`.

### Malloc failure mode

|Flag                    |  Check                                          |
|------------------------|-------------------------------------------------|
| `--malloc-fail-null`   |  in case malloc fails return NULL               |
| `--malloc-fail-assert` |  in case malloc fails report as failed property |
| `--malloc-may-fail`    |  malloc may non-deterministically fail          |

Calling `malloc` may fail for a number of reasons and the function may return a
NULL pointer. The users can choose if and how they want the `malloc`-related
failures to occur. The option `--malloc-fail-null` results in `malloc` returning
the NULL pointer when failing. The option `--malloc-fail-assert` places
additional properties inside `malloc` that are checked and if failing the
verification is terminated (by `assume(false)`). One such property is that the
allocated size is not too large, i.e. internally representable. When neither of
those two options are used, CBMC will assume that `malloc` does not fail.

Malloc may also fail for external reasons which are not modelled by CProver. If
you want to replicate this behaviour use the option `--malloc-may-fail` in
conjunction with one of the above modes of failure.

These malloc failure options need to be set when the C library model is added to
the program. Typically this is upon invoking CBMC, but if the user has chosen to
do so via `goto-instrument --add-library`, then the malloc failure mode needs to
be specified with that `goto-instrument` invocation, i.e., as an option to
`goto-instrument`.
