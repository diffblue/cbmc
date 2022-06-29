[CPROVER Manual TOC](../)

# Modular Verification of Static Functions

This page describes how to use CBMC on static functions.

CBMC can check libraries and other codebases that expose several
entry points. To do this, users typically write a *harness* that
captures the entry points' API contract, and that calls into the API
with unconstrained values. The example below shows such a library and
harness:

```C
void public_api_function(const int *a, int *b)
{
  // ...
  private_function(a, b);
  // ...
}

static void private_function(const int *a, int *b)
{
  // ...
}
```

The harness sets up some assumptions and then calls into the API:

```C
void public_api_function(int *a, int *b);

void harness()
{
  int a, b;
  __CPROVER_assume(a < 10);
  __CPROVER_assume(a >= 0);
  public_api_function(&a, &b);
  __CPROVER_assert(b != a);
}
```

The following commands build and check this function:

```sh
> goto-cc -c -o library.o library.c
> goto-cc -c -o harness.o harness.c
> goto-cc -o to_check.gb library.o harness.o
> cbmc --function harness to_check.gb
```

## Stubbing out static functions

For performance reasons, it might be desirable to analyze the API
function independently of the static function. We can analyze the API
function by "stubbing out" the static function, replacing it with a
function that does nothing apart from asserting that its inputs satisfy
the function's contract. ("Stubbing out" a function is sometimes known
as "modelling" or "abstracting it out".) Add the following to
`harness.c`:

```C
static void private_function(const int *a, int *b)
{
  __CPROVER_assert( private_function_precondition );
  __CPROVER_assume( private_function_postcondition );
}
```

And build as follows, stripping the original static function out of its
object file:

```sh
> goto-cc -c -o library.o library.c
> goto-instrument --remove-function-body private_function library.o library-no-private.o
>
> goto-cc -c -o harness.o harness.c
>
> # The stub in the harness overrides the implementation of
> # private_function whose body has been removed
> goto-cc -o to_check.gb library-no-private.o harness.o
> cbmc --function harness to_check.gb
```

## Separately checking static functions

We should now also write a harness for `private_function`. However,
since that function is marked `static`, it is not possible for functions
in external files to call it. We can write and link a harness by
stripping the `static` attribute from `private_function` using goto-cc's
`--export-file-local-symbols` flag.

```sh
> goto-cc -c -o --export-file-local-symbols library_with_static.o library.c
```

`library_with_static.o` now contains an implementation of `private_function()`
with a mangled name. We can display the mangled name with goto-instrument:

```sh
> goto-instrument --show-symbol-table library_with_static.o | grep -B1 -A1 "Pretty name.: private_function"
Symbol......: __CPROVER_file_local_library_c_private_function
Pretty name.: private_function
Module......: private_function
```

When we write a harness for the static function, we ensure that we call
the mangled name:

```C
void harness()
{
  int a, b;

  __CPROVER_assume( private_function_precondition );

  // Call the static function
  __CPROVER_file_local_library_c_private_function(&a, &b);

  __CPROVER_assert( private_function_postcondition );
}
```

We can then link this harness to the object file with exported symbols
and run CBMC as usual.

```sh
> goto-cc -c -o private_harness.o private_harness.c
> goto-cc -o to_test.gb private_harness.o library_with_static.o
> cbmc --function harness to_test.gb
```


It is possible that CBMC will generate the same mangled name for two
different static functions. This happens when the functions have the
same name and are written in same-named files that live in different
directories. In the following codebase, the two `qux` functions will
both have their names mangled to `__CPROVER_file_local_b_c_qux`, and
so any harness that requires both of those files will fail to link.

```
    project
    |
    \_ foo
    |  |
    |  \_ a.c
    |  \_ b.c <- contains static function "qux"
    |
    \_ bar
       |
       \_ c.c
       \_ b.c <- also contains static function "qux"
 ```

The solution is to use the `--mangle-suffix` option to goto-cc. This
allows you to specify a different suffix for name-mangling. By
specifying a custom, different suffix for each of the two files, the
mangled names are unique and the files can be successfully linked.

More examples are in `regression/goto-cc-file-local`.
