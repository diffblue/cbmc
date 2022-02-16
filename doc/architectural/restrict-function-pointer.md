[CPROVER Manual TOC](../../)

## Restricting function pointers

In this document, we describe the `goto-instrument` feature to replace calls
through function pointers by case distinctions over calls to given sets of
functions.

### Motivation

The CPROVER framework includes a goto program transformation pass
`remove_function_pointers()` to resolve calls to function pointers to direct
function calls. The pass is needed by `cbmc`, as symbolic execution itself can't
handle calls to function pointers. In practice, the transformation pass works as
follows:

Given that there are functions with these signatures available in the program:

```
int f(int x);
int g(int x);
int h(int x);
```

And we have a call site like this:

```
typedef int(*fptr_t)(int x);
void call(fptr_t fptr) {
  int r = fptr(10);
  assert(r > 0);
}
```

Function pointer removal will turn this into code similar to this:

```
void call(fptr_t fptr) {
  int r;
  if(fptr == &f) {
    r = f(10);
  } else if(fptr == &g) {
    r = g(10);
  } else if(fptr == &h) {
    r = h(10);
  } else {
    // sanity check
    assert(false);
    assume(false);
  }
  return r;
}
```

This works well enough for simple cases. However, this is a very simple
replacement only based on the signature of the function (and whether or not they
have their address taken somewhere in the program), so if there are many
functions matching a particular signature, or if some of these functions are
expensive in symex (e.g. functions with lots of loops or recursion), then this
can be a bit cumbersome - especially if we, as a user, already know that a
particular function pointer will only resolve to a single function or a small
set of functions. The `goto-instrument` option `--restrict-function-pointer`
allows to manually specify this set of functions.

### Example

Take the motivating example above. Let us assume that we know for a fact that
`call` will always receive pointers to either `f` or `g` during actual
executions of the program, and symbolic execution for `h` is too expensive to
simply ignore the cost of its branch. For this, we will label the places in each
function where function pointers are being called, to this pattern:

```
<function-name>.function_pointer_call.<N>
```
where `N` is referring to which function call it is - so the first call to a
function pointer in a function will have `N=1`, the 5th `N=5` etc, or
```
<function-name>.<label>
```
when the function call is labelled.

We can call `goto-instrument --restrict-function-pointer
call.function_pointer_call.1/f,g in.gb out.gb`. This can be read as

> For the first call to a function pointer in the function `call`, assume that
> it can only be a call to `f` or `g`

The resulting output (written to goto binary `out.gb`) looks similar to the
original example, except now there will not be a call to `h`:

```
void call(fptr_t fptr) {
  int r;
  if(fptr == &f) {
    r = f(10);
  } else if(fptr == &g) {
    r = g(10);
  } else {
    // sanity check
    assert(false);
    assume(false);
  }
  return r;
}
```

Another example: Imagine we have a simple virtual filesystem API and implementation
like this:

```
typedef struct filesystem_t filesystem_t;
struct filesystem_t {
  int (*open)(filesystem_t *filesystem, const char* file_name);
};

int fs_open(filesystem_t *filesystem, const char* file_name) {
  filesystem->open(filesystem, file_name);
}

int nullfs_open(filesystem_t *filesystem, const char* file_name) {
  return -1;
}

filesystem_t nullfs_val = {.open = nullfs_open};
filesystem *const nullfs = &nullfs_val;

filesystem_t *get_fs_impl() {
  // some fancy logic to determine
  // which filesystem we're getting -
  // in-memory, backed by a database, OS file system
  // - but in our case, we know that
  // it always ends up being nullfs
  // for the cases we care about
  return nullfs;
}
int main(void) {
  filesystem_t *fs = get_fs_impl();
  assert(fs_open(fs, "hello.txt") != -1);
}
```

In this case, the assumption is that *we* know that in our `main`, `fs` can be
nothing other than `nullfs`; But perhaps due to the logic being too complicated
symex ends up being unable to figure this out, so in the call to `fs_open()` we
end up branching on all functions matching the signature of
`filesystem_t::open`, which could be quite a few functions within the program.
Worst of all, if its address is ever taken in the program, as far as the "dumb"
function pointer removal is concerned it could be `fs_open()` itself due to it
having a matching signature, leading to symex being forced to follow a
potentially infinite recursion until its unwind limit.

In this case we can again restrict the function pointer to the value which we
know it will have:

```
--restrict-function-pointer fs_open.function_pointer_call.1/nullfs_open
```

### Loading from file

If you have many places where you want to restrict function pointers, it'd be a
nuisance to have to specify them all on the command line. In these cases, you
can specify a file to load the restrictions from instead, via the
`--function-pointer-restrictions-file` option, which you can give the name of a
JSON file with this format:

```
{
  "function_call_site_name": ["function1", "function2", ...],
   ...
}
```

**Note:** If you pass in multiple files, or a mix of files and command line
restrictions, the final restrictions will be a set union of all specified
restrictions.

**Note:** as of now, if something goes wrong during type checking (i.e. making
sure that all function pointer replacements refer to functions in the symbol
table that have the correct type), the error message will refer to the command
line option `--restrict-function-pointer` regardless of whether the restriction
in question came from the command line or a file.
