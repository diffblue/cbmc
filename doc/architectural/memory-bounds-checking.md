\ingroup module_hidden
\page memory-bounds-checking Memory Bounds Checking

cbmc provides means to verify that pointers are within the bounds of (statically
or dynamically) allocated memory blocks. When the option `--pointer-check` is
used, cbmc checks the safety of each pointer dereference in the program.
Similarly, the primitive `__CPROVER_r_ok(pointer, size)` returns true when it is
safe to read from the memory segment starting at `pointer` and extending for
`size` bytes. `__CPROVER_w_ok(pointer, size)` indicates if writing to the given
segment is safe. At present, both primitives behave the same.

Each memory segment is referred to internally in cbmc via an object id. Pointers
are represented as bitvectors (typically of length 32 or 64). The topmost `n`
bits encode the id of the memory segment the pointer is pointing to, and the
remaining bits encode the offset within the segment. The number of bits used to
represent the object id can be specified via `--object-bits n`. Object offsets
are signed. This allows to distinguish the case of when a pointer has been
incremented too much from the case of when a pointer has been decremented too
much. In the latter case, a negative value would be visible for the offset
portion of a pointer in an error trace.

In the following, we describe how the memory bounds checks are implemented in
cbmc for dynamically allocated memory. Dynamic memory is allocated in C via the
`malloc()` library function. Its model in cbmc looks as follows (see
`src/ansi-c/library/stdlib.c`, details not related to memory bounds checking are
left off):

```C
inline void *malloc(__CPROVER_size_t malloc_size)
{
  void *malloc_res;
  malloc_res = __CPROVER_allocate(malloc_size, 0);

  __CPROVER_bool record_malloc = __VERIFIER_nondet___CPROVER_bool();
  __CPROVER_malloc_object = record_malloc ? malloc_res : __CPROVER_malloc_object;

  return malloc_res;
}
```

The internal variable `__CPROVER_malloc_object`
is initialized to 0 in the `__CPROVER_initialize()` function of a goto program.
The nondeterministic switch controls whether the address of the memory
block allocated in this particular invocation of `malloc()` is recorded.

When the option `--pointer-check` is used, cbmc generates the following
verification condition for each pointer dereference expression (e.g.,
`*pointer`):

```C
__CPROVER_POINTER_OFFSET(pointer) >= 0 &&
__CPROVER_POINTER_OFFSET(pointer) < __CPROVER_OBJECT_SIZE(pointer)
```

The primitives `__CPROVER_POINTER_OFFSET()` and `__CPROVER_OBJECT_SIZE()` extract
the pointer offset and size of the object pointed to, respectively. Similar conditions are
generated for `assert(__CPROVER_r_ok(pointer, size))` and
`assert(__CPROVER_w_ok(pointer, size))`.

To illustrate how the bounds checking works, consider the following example
program which is unsafe:


```C
int main()
{
  char *p1 = malloc(1);
  p1++;
  char *p2 = malloc(2);

  *p1 = 1;
}
```

Here the verification condition generated for the pointer dereference should
fail. In the approach outlined above it indeed can, as one can choose true for
`__VERIFIER_nondet___CPROVER_bool()` in the first call
to `malloc()`, and false for `__VERIFIER_nondet___CPROVER_bool()` in the second
call to `malloc()`. Thus, the object address of the first call to
`malloc()` is recorded in `__CPROVER_malloc_object`.
