# Frees Clauses {#contracts-frees}

# Frees Clauses

A _frees clause_ allows the user to specify a set of pointers that may be freed
by a function or by the function it calls, transitively.
A function contract may have zero or more frees clauses.
When no clause is provided the empty set is used as default.
Contracts can also have an empty frees clause.
When more than one frees clause is given, the sets of pointers they contain are
unioned together to yield a single set of pointers.

## Syntax

The clause has the following syntax (square brackets denote optional expressions
`[` `]` ):
```c
__CPROVER_frees([targets])
```

Where `targets` has the following syntax:
```
          targets ::= cond-target-group (';' cond-target-group)* ';'?
cond-target-group ::= (condition ':')? target (',' target)*
           target ::= lvalue-expr
                    | __CPROVER_freeable(lvalue-expr)
```

A frees clause target must be either:
- an lvalue expression with a pointer type,
- a call to the built-in function `__CPROVER_freeable`
- a call to a user-defined side effect free and deterministic function returning
  the type `void` (itself containing direct or indirect calls to
  `__CPROVER_freeable` or to functions that call `__CPROVER_freeable`);

### Example

```c
int foo(char *arr1, char *arr2, size_t size)
__CPROVER_frees(
    // `arr1` is freeable only if the condition `size > 0 && arr1` holds
    size > 0 && arr1: arr1;

    // `arr2` is always freeable
    arr2;
)
{
  if(size > 0 && arr1)
    free(arr1);
  free(arr2);
  return 0;
}
```

## Semantics

The set of pointers specified by the frees clause of the contract is interpreted
at the function call-site where the contract is being checked or used to abstract
a function call.

### For contract checking

When checking a contract against a function, each pointer that the
function attempts to free gets checked for membership in the set of
pointers specified by the _frees clause_.

### For replacement of function calls by contracts

When replacing a function call by a contract, each pointer of the
_frees clause_ gets non-deterministically freed between the evaluation of
preconditions and before the evaluation of post-conditions.

## Specifying parametric sets of freeable pointers using C functions

Users can define parametric sets of freeable pointers by writing functions that
return the `void` type and call (directly or indirectly) the built-in function
`__CPROVER_freeable`:

```c
void my_freeable_set(char **arr, size_t size)
{
  // The first 3 pointers are freeable
  // if the array is at least of size 3.
  if (arr && size > 3) {
    __CPROVER_freeable(arr[0]);
    __CPROVER_freeable(arr[1]);
    __CPROVER_freeable(arr[2]);
  }
}
```

Calling the built-in function:
```c
void __CPROVER_freeable(void *ptr);
```
in the context of a frees clause specifies that `ptr` is freeable in that
context.

```c
void my_function(char **arr, size_t size)
__CPROVER_frees(
  // arr is considered freeable in the context of this clause.
  my_freeable_set(arr, size)
)
{
  // body ...
}
```

## Frees clause related predicates

The predicate:
```c
__CPROVER_bool __CPROVER_is_freeable(void *ptr);
```
can only be used in pre and post conditions, in contract checking or replacement
modes. It returns `true` if and only if the pointer satisfies the preconditions
of the `free` function from `stdlib.h`
([see here](https://github.com/diffblue/cbmc/blob/cf00a53bbcc388748be9668f393276f6d84b1a60/src/ansi-c/library/stdlib.c#L269)),
that is if and only if the pointer points to a valid dynamically allocated object and has offset zero.

The predicate:
```c
__CPROVER_bool __CPROVER_was_freed(void *ptr);
```
can only be used in post conditions and returns `true` if and only if the
pointer was freed during the execution of the function under analysis.
