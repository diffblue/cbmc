# Rewriting Declarative Assign and Frees Specification Functions {#contracts-dev-spec-spec-rewriting}

Back to top @ref contracts-dev-spec

@tableofcontents

The front end allows to express parametric assignable sets and freeable sets
declaratively by calling special built-ins from regular C functions,
as described in @ref contracts-assigns and @ref contracts-frees.

Such functions require a rewriting pass in order to turn them into active
functions that can effectively populate a write set with new targets.

## Rewriting Assigns Clause Functions {#contracts-dev-spec-spec-rewriting-assigns}

GOTO functions which specify assignable locations have the following type
signature:

```c
void foo(parameter-list);
```

They can be generated from an assigns clause or written by the user.

To convert them to active functions, the first step is to inline their body and
remove all function calls, the result of which must be loop-free.

Then, a second pass adds the write set to be filled as new parameter to the
function:

```c
void foo(
  foo-parameters,

  // write set to populate with new targets
  __CPROVER_contracts_write_set_ptr_t __write_set_to_fill);
```

In the inlined body, calls to built in functions `__CPROVER_assignable`,
`__CPROVER_object_upto`, `__CPROVER_object_from`, `__CPROVER_object_whole`
are numbered from 0 to N in increasing order from their position in the
instruction sequence:

```c
CALL __CPROVER_object_upto(ptr, size); // index 0
CALL __CPROVER_object_whole(ptr); // index 1
CALL __CPROVER_object_from(ptr); // index 2
...
CALL __CPROVER_assignable(ptr, size, is_ptr_to_ptr); // index N
```

They are then rewritten into calls to the corresponding instrumentation hook
provided by the @ref cprover_contracts.c library:

```c
CALL __CPROVER_contracts_write_set_insert_object_upto(
  __write_set_to_fill, 0, ptr, size);
CALL __CPROVER_contracts_write_set_insert_object_whole(
  __write_set_to_fill, 1, ptr);
CALL __CPROVER_contracts_write_set_insert_object_from(
  __write_set_to_fill, 2, ptr);
...
CALL __CPROVER_contracts_write_set_insert_assignable(
       __write_set_to_fill, N, ptr, size, is_ptr_to_ptr);
```

The function is then instrumented as described in
@ref contracts-dev-spec-dfcc-instrument which adds a second write set parameter,
that allows to check that the function has no unintended side effects.

```c
void foo(
 <parameter-list>,

 // write set to populate with new targets
 __CPROVER_contracts_write_set_ptr_t __write_set_to_fill,

 // write set against which to check itself for unwanted side effects
  __CPROVER_contracts_write_set_ptr_t __write_set_to_check);
```


## Generating Havoc Functions from Assigns Clause Functions {#contracts-dev-spec-spec-rewriting-havoc}

Contract replacement requires havocing the set of targets described in an
assigns clause. Since there can exist dependencies and aliasing between the
different targets, in order to havoc them in parallel, we first need to snapshot
the target locations into a write set data structure, and generate a function
that can havoc these snapshotted locations in a second step.

GOTO functions which specify assignable locations have the following type
signature:

```c
void foo(parameter-list);
```

They can be generated from an assigns clause or written by the user.

To convert them to havoc functions, the first step is to inline their body and
remove all function calls, the result of which must be loop-free.

Then, a second pass adds the write set to be havoced as new parameter to the
function:

```c
void contract::foo::havoc(
  // write set containing snapshots of the targets to havoc
  __CPROVER_contracts_write_set_ptr_t __write_set_to_fill);
```

In the inlined body, calls to built in functions `__CPROVER_assignable`,
`__CPROVER_object_upto`, `__CPROVER_object_from`, `__CPROVER_object_whole`
are numbered from 0 to N in increasing order from their position in the
instruction sequence:

```c
CALL __CPROVER_object_upto(ptr, size); // index 0
CALL __CPROVER_object_whole(ptr); // index 1
CALL __CPROVER_object_from(ptr); // index 2
...
CALL __CPROVER_assignable(ptr, size, is_ptr_to_ptr); // index N
```

They are then rewritten into calls to the corresponding instrumentation hook
provided by the @ref cprover_contracts.c library:

Targets specified with `__CPROVER_object_whole`:

```c
CALL __CPROVER_object_whole(ptr); // at index i
```

Get rewritten to:
```c
CALL __CPROVER_contracts_havoc_object_whole(write_set, i);
```

Targets specified with `__CPROVER_object_from` or `__CPROVER_object_upto`:

```c
CALL __CPROVER_object_from(ptr); // at index i
```

Get rewritten to:

```c
CALL __CPROVER_contracts_havoc_slice(write_set, i);
```

Last, targets specified with `__CPROVER_assignable`

```c
CALL __CPROVER_assignable(ptr, size, is_ptr_to_ptr); // at index i
```

Get rewritten to a typed nondeterministic assignment:

```c
CALL void *target = __CPROVER_contracts_write_set_havoc_get_assignable_target(write_set, i);
ASSIGN *target = nondet_type_of_target();
```

The generated function has the intended side effects by construction and nothing
else.

## Rewriting Frees Clause Functions {#contracts-dev-spec-spec-rewriting-frees}

User-defined functions which list freeable pointers have the following signature:

```c
void foo(<parameter-list>);
```

They are first inlined and checked to be loop free before being rewritten into
functions which accepts a write set parameter to be filled with freeable targets
defined by the function:

```c
void foo(
 <parameter-list>,

 // write set to populate with new targets
 __CPROVER_contracts_write_set_ptr_t __write_set_to_fill);
```

Calls to the built-in function:

```c
CALL __CPROVER_freeable(ptr);
```

are rewritten into to calls to active instrumentation functions which insert into the write set

```c
CALL __CPROVER_contracts_write_set_add_freeable(
  __write_set_to_fill, ptr);
```

The function is then instrumented as described in
@ref contracts-dev-spec-dfcc-instrument which adds a second write set parameter,
that allows to check that the function has no unintended side effects.

```c
void foo(
 <parameter-list>,

 // write set to populate with new targets
 __CPROVER_contracts_write_set_ptr_t __write_set_to_fill,

 // write set against which to check itself for unwanted side effects
  __CPROVER_contracts_write_set_ptr_t __write_set_to_check);
```

---
 Prev | Next
:-----|:------
 @ref contracts-dev-spec-codegen | @ref contracts-dev-spec-memory-predicates-rewriting