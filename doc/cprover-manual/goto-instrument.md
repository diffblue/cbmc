[CPROVER Manual TOC](../)

## Goto Instrument

This is a tool that implements a variety of instrumentation passes modifying a
pre-existing GOTO binary, or rather producing the modified binary as output.

```sh
$ goto-instrument in.gb out.gb <instrumentation-options>
```

### Diagnosis Options

### Safety Checks

### Semantic Transformations

#### Generate Function Body

This transformation inserts implementation of functions without definition, i.e.
a body. The user is allowed to choose the behavior to be implemented by those
functions from a predefined list. The command-line option to select the behavior
is `--generate-function-body-options <option>`.

- `assert-false`: The body consists of a single command: `assert(0);`
- `assume-false`: The body consists of a single command: `assume(0);`
- `nondet-return`: The body only returns a non-deterministic value of it's
  return type.
- `assert-false-assume-false`: Two commands as above.
- `havoc[,params:<p-regex>][,globals:<g-regex>]`: Assign non-deterministic
  values to the targets of pointer-to-non-constant parameters matching the
  `p-regex`, and non-constant globals matching the `g-regex` and then (in case
  of non-void function) returning as with `nondet-return`.

Let's demonstrate using the havoc on a simple example:

```C
// main.c
int global;
const int c_global;

int function(int *param, const int *c_param);
```

Often we want to avoid overwriting internal symbols, i.e. those with `__`
prefix, which is done using the pattern `(?!__)`.

```sh
$ goto-cc main.c -o main.gb
$ goto-instrument main.gb main-out.gb \
  --generate-function-body-options 'havoc,params:(?!__).*,globals:(?!__).*' \
  --generate-funtion-body function
```

Leads to a binary equivalent to the following C code:

```C
// main-mod.c
int function(int *param, const int *c_param) {
  *param = nondet_int();
  global = nondet_int();
  return nondet_int();
}
```

Which parameters should be modified can be specified either by a regular
expression (as above) or by a semicolon-separated list of their numbers. For
example `havoc,params:0;3;4` will assign non-deterministic values to the 1st,
4th, and 5th parameter.

Finally, the user can also request different implementation for a number of
call-sites of a single function. The option `--generate-havocing-body` inserts
new functions for selected call-sites and replaces the calls to the origin
function with calls to the respective new functions.

```C
// main.c
int function(int *first, int *second, int *third);

int main() {
  int a = 10;
  int b = 10;
  int c = 10;

  function(&a, &b, &c);
  function(&a, &b, &c);
}
```

The user can specify different behavior for each call-site as follows:

```
$ goto-cc main.c -o main.gb
$ goto-instrument main.gb  main-mod.gb \
  --generate-havocing-body 'function,1,params:0;2,2,params:1'
```

Results in a binary equivalent to:

```C
// main-mod.c
int function_1(int *first, int *second, int *third) {
  *first = nondet_int();
  *third = nondet_int();
}

int function_2(int *first, int *second, int *third) {
  *second = nondet_int();
}

int main() {
  int a = 10;
  int b = 10;
  int c = 10;

  function_1(&a, &b, &c);
  function_2(&a, &b, &c);
}
```

Note that only parameters of pointer type can be havoc(ed) and CBMC will produce
an error report if given a parameter number associated with a non-pointer
parameter. Requesting to havoc a parameter with a number higher than the number
of parameters a given function takes will also results in an error report.

### Loop Transformations

### Memory Model Instrumentations

### Slicing

### Further Transformations
