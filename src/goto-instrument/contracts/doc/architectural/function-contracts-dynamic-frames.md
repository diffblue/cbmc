\ingroup module_hidden

\page dfcc Function Contracts and Dynamic Frame Condition Checking

\tableofcontents

This page describes how support for function contracts is implemented by
classes found in the folder `goto-instrument/contracts/dynamic-frames/`.

\section dfcc-function-contracts-in-cbmc Overview of Function Contracts in CBMC

\subsection dfcc-function-contracts-syntax Syntax of contracts in CBMC

In CBMC, function contracts are specified by attaching one or more
specification clauses to a function declaration or definition.

The full user documentation for function contracts can be found [here](http://www.cprover.org/cprover-manual/contracts/functions),
However, to make this page self-contained, we briefly remind the types of clauses below:

```c
ret_t foo(parameters)
__CPROVER_requires(R)
__CPROVER_ensures(E)
__CPROVER_requires_contract(P, C)
__CPROVER_ensures_contract(P, C)
__CPROVER_assigns(A)
__CPROVER_frees(F)
;
```

- Specifying preconditions:
  - A _requires_ clause specifies a precondition as boolean expression R that may
  only depend on program globals and function parameters;
  - A _requires contract_ clause specifies the precondition that a function pointer
  expression P satisfies a contract C, and where P may only depend on program globals
  and function parameters;
- Specifying postconditions:
  - An _ensures_ clause specifies a postcondition as boolean expression E that may
  only depend on program globals, function parameters, history variables and the
  special variable `__CPROVER_return_value` and defines the contract's
  postconditions.
  - An _ensures contract_ clause specifies the postcondition that a function pointer
  expression P satisfies a contract C, and where P may only depend on program globals,
  function parameters, history variables and the special variable `__CPROVER_return_value`;
- Specifying frame conditions:
  - An _assigns_ clause specifies a set A of memory locations that may be
  assigned to by any function satisfying the contract. The syntax used to define elements of A
  is documented [here](../cprover-manual/contracts-assigns.md).
  - The _frees_ clause of the contract specifies the set `F` of pointers to dynamic objects
  that may be freed by any function satisfying the contract. The syntax used to define elements of E
  is documented [here](../cprover-manual/contracts-assigns.md).

For each such `foo` carrying contract clauses, the ansi-c front-end
creates a function symbol named `contract:foo` in the GOTO model's symbol table,
with the same signature as `foo`, and moves the contract clauses to that new symbol.
We call `contract:foo` the **pure contract** associated with the function `foo`.


\subsection dfcc-contract-checking Checking a Contract Against a Function

Let us consider a contract `c`, a function `foo` and a proof harness `main`.

```c
// A contract
int c(int *a, int *b)
__CPROVER_requires(R)
__CPROVER_ensures(E)
__CPROVER_assigns(A)
__CPROVER_frees(F)
;

// A function
int foo(int *a, int *b)
{
  // does something with a and b
}


// A proof harness
void main()
{
  // allocate non-deterministic parameters
  int *a = ...;
  int *b = ...;

  // call the function under verification
  foo(a, b);
}
```

In order to check the contract `c` against `foo` in the context of `main`,
we first create a fresh function `foo_swapped` with the same interface as
`foo` and swap the body of `foo` into `foo_swapped`, while instrumenting it
to check that only locations allowed by the assigns clause are actually assigned
to, and that only pointers specified in the frees clause are freed.

```c
// The old foo function
int foo_swapped(int *a, int *b)
{
  // does something with a and b (now checked against A and F)
}
```

Then, a new body for `foo` is generated as follows:

```c
// The new foo, checking `c` against `foo_swapped`
int foo(int *a, int *b) {
  // Assume preconditions
  assume(R);

  // Snapshot history variables
  hist1_t histt1 = nondet();
  hist2_t hist2 = nondet();
  // ...

  // Call function under verification
  int retval = foo_swapped(a, b);

  // Check postconditions
  assert(E);

  // Return the return value
  return retval;
}
```

After this swap-and-wrap operation, the `main` function effectively calls the
contract-checking wrapper. Analysing this model with CBMC will effectively check
that the initial `foo`, under the assumption that the contract preconditions hold,
satisfies the frame conditions, and satisfies the postconditions.

\subsection dfcc-contract-replacement Replacing a Function by a Contract

Let us now consider a function `bar`, called directly or indirectly from `main`.
We now want to replace `bar` with an abstraction derived from a contract `d`.

```c
// A contract
int d(int *a)
__CPROVER_requires(R)
__CPROVER_ensures(E)
__CPROVER_assigns(A)
__CPROVER_frees(F)
;

// A function
int bar(int *a)
{
  // does something with a;
}
```

We abstract `bar` by replacing its instructions with instructions modelling
the behavior of the contract `d`:

```c
int bar(int *a)
{
  // Check preconditions
  assert(R);

  // Snapshot history variables
  hist1_t histt1 = nondet();
  hist2_t hist2 = nondet();
  // ...

  // Havoc assignable memory locations
  // for a1, a2, ... in A
  a1 = nondet_t1();
  a2 = nondet_t2();
  // ...

  // Generate nondet return value
  int retval = nondet();

  // Free freeable pointers
  // for ptr1, ptr2 in F
  if(nondet_bool())
    free(ptr1);

  if(nondet_bool())
    free(ptr2);
  // ...

  // Assume postconditions
  assume(E);

  // Returnt return value
  return retval;
}
```

Any function that used to call the initial `bar` now calls the abstraction
derived from the contract.

\section dfcc-implementation Function Contracts Implementation

The classes found in folder `goto-instrument/contracts/dynamic-frames` implement
contract checking and replacement with frame condition checking as a single
`goto-instrument` pass.

This `goto-instrument` pass takes the following inputs:
- `harness` : identifier of the proof harness;
- `to_check`: an optional pair `f_top -> c_top` where `f_top` is a function
  called from the harness, and `c_top` is the contract to check against `f_top`;
- `to_replace`: a set of pairs `f -> c` where `f` is a function and `c` is a
  contract to be used as replacement for `f`. Functions `f` will typically be
  functions called by `f_top` that need to be abstracted away with contracts.

For frame conditions checking we use a method inspired by the notion of
[Dynamic Frames](https://pm.inf.ethz.ch/publications/Kassios11.pdf).

The method consists in modelling sets of assignable and freeable memory
locations as ghost data structures embedded in the program. More precisely,
a dynamic frame tracks 4 sets of memory locations:

```
dynamic_frame = (contract_assigns, contract_frees, allocated, deallocated)
```

Where:
- `contract_assigns` is the set of memory locations specified in the *assigns clause* of the contract of interest,
- `contract_frees` is the set of pointers specified in the *frees clause* of the contract of interest,
- `allocated` is the set objects identifiers allocated on the stack or the heap during program execution,
- `deallocated` is the set of pointers deallocated during program execution.

The dynamic frame data structure is accompanied by functions allowing
to add elements to or remove elements from the various sets,
to checks if a memory location is included in one of the memory locations
tracked by a dynamic frame, to perform inclusion checks of all memory locations
of a dynamic frame in memory locations of another dynamic frame, etc.

The instrumentation pass transforms all user-defined GOTO functions and library
functions by adding an extra parameter that is a pointer to a dynamic
representation of the sets introduced above:

```c
ret_t f(<original-parameters>,  dynamic_frame);
```

Function bodies is instrumented so that
- when the write_set pointer is NULL no checks are performed,
- when it is not NULL the following checks are performed
  * Assignments LHS are checked for inclusion in `contract_assigns` or `allocated`,
  * DECL objects are recorded in `allocated`
  * Dynamically allocated objects are recorded in `allocated`
  * DEAD objects or objects assigned to `__CPROVER_dead_object` are removed from `allocated`
  * dynamic objects deallocated with `__CPROVER_deallocate` are checked for inclusion in `contract_frees` or `allocated`, and recorded in `deallocated` (so that if needed we can check in post conditions that the function indeed deallocated the expected memory).
  * The current write set is propagated to all functions calls or function pointer calls.

Since the write set is dynamically updated, a same function called at different call sites can see a different write set.

Write sets are initialised from contracts descriptions and injected in function calls that are checked against contracts, or used to perform inclusion checks against write sets obtained from callers for functions that are replaced by a contract. 

* * *

# Usage example

```c
#include <stdbool.h>
#include <stdlib.h>

// specifies the assignable set for bar
__CPROVER_assignable_t bar_assigns(char *arr, size_t size) {
  if (size > 0)
   __CPROVER_typed_target(arr[0]);
  if (size > 1)
    __CPROVER_typed_target(arr[1]);
  if (size > 2)
    __CPROVER_typed_target(arr[2]);
}

// specifies the freeable set for bar
__CPROVER_freeable_t bar_frees(char *arr, size_t size) {
  __CPROVER_freeable(arr);
}

// bar gets replaced
int bar(char *arr, size_t size)
    // clang-format off
__CPROVER_requires(size > 0 && __CPROVER_is_freshr(&arr, size))
__CPROVER_assigns(bar_assigns(arr, size))
__CPROVER_frees(bar_frees(arr, size))
__CPROVER_ensures(true)
// clang-format on
{
  arr[0] = 0;
  if (size > 1)
    arr[1] = 0;
  if (size > 2)
    arr[2] = 0;
}

// assignable set for foo
__CPROVER_assignable_t foo_assigns(char *arr, size_t size) {
  if (arr && size > 0)
    __CPROVER_typed_target(arr[0]);
  if (arr && size > 1)
    __CPROVER_typed_target(arr[1]);
}

// freeable set for foo
__CPROVER_freeable_t foo_frees(char *arr, size_t size) {
  if (arr)
    __CPROVER_freeable(arr);
}

// precondition for foo
bool foo_precondition(const char **arr, const size_t size) {
  return size > 0 && __CPROVER_is_freshr(arr, size);
}

// foo gets checked against its contract
int foo(char *arr, size_t size)
    // clang-format off
__CPROVER_requires(foo_precondition(&arr, size))
__CPROVER_assigns(foo_assigns(arr, size))
__CPROVER_frees(foo_frees(arr, size))
__CPROVER_ensures(1)
// clang-format on
{
  if (arr && size > 0)
    arr[0] = 0;
  if (arr && size > 1)
    arr[1] = 0;
     // violates assigns clause
  if (arr && size > 5)
    arr[5] = 0;

  int result = 0;

   // bar gets replaced by its contract
   // inclusion check fails
  result = bar(arr, size);

  // possible invalid and double-free
  //git  because bar can free arr
  free(arr); 

  return result;
}

int main() {
  size_t size;
  char *arr = NULL;
  foo(arr, size);
  return 0;
}
```

## Command line usage

```
❯ goto-cc main.c -o main.o
❯ goto-instrument --dyncontracts main \
                  --enforce-contract foo\
                  --replace-call-with-contract bar\
                  main.o\
                  main-mod.o
❯ cbmc main-mod.o
...

** Results:

[bar.assigns.1] Check that the assigns clause of contract::bar 
   is included in the caller's assigns clause: FAILURE

[bar.frees.1] Check that the frees clause of contract::bar 
   is included in the caller's frees clause: SUCCESS

[free.frees.1] line 36 Check that deallocation of ptr 
   is allowed by the frees clause: FAILURE

[foo.postcondition.1] line 60 Check ensures clause of contract contract::foo 
  for function foo: SUCCESS

[foo.assigns.1] line 64 Check that arr[(signed long int)0] 
  is allowed by the assigns clause: SUCCESS
[foo.assigns.2] line 66 Check that arr[(signed long int)1] 
  is allowed by the assigns clause: SUCCESS
[foo.assigns.3] line 69 Check that arr[(signed long int)5] 
  is allowed by the assigns clause: FAILURE
[foo.assigns.4] line 71 Assignment to local symbol result implicitly allowed: SUCCESS
[foo.assigns.5] line 75 Assignment to local symbol result implicitly allowed: SUCCESS

[foo.precondition_instance.1] line 78 free argument must be NULL or valid pointer: FAILURE
[foo.precondition_instance.2] line 78 free argument must be dynamic object: SUCCESS
[foo.precondition_instance.3] line 78 free argument has offset zero: SUCCESS
[foo.precondition_instance.4] line 78 double free: FAILURE
[foo.precondition_instance.5] line 78 free called for new[] object: SUCCESS
[foo.precondition_instance.6] line 78 free called for stack-allocated object: SUCCESS

[foo_precondition.assigns.1] line 51 Assignment to local symbol return_value___CPROVER_is_freshr implicitly allowed: SUCCESS
[foo_precondition.assigns.2] line 51 Assignment to local symbol tmp_if_expr implicitly allowed: SUCCESS
[foo_precondition.assigns.3] line 51 Assignment to local symbol tmp_if_expr implicitly allowed: SUCCESS
```

* * *

# Front-end updates

Files:
-  Files `src/ansi-c`
- `goto-programs/goto_convert.cpp`
- `linking/remove_internal_symbols.cpp`
- `util/c_types.h`
- `util/ire_ids.def`

## Specifying assignable locations declaratively with `__CPROVER_assignable_t` functions in C

We provide a new built-in type meant to be used as a return type for functions that describe sets of assignable memory locations:

```c
typedef void __CPROVER_assignable_t;
```

We also provide the following built-ins:

```c
// Specifies that the range of `size` bytes starting at the address stored `ptr` 
// (the range must to be completely within the bounds of the object of `ptr`)
__CPROVER_assignable_t __CPROVER_object_upto(void *ptr, __CPROVER_size_t size);

// Syntactic sugar for:
// __CPROVER_obj_upto(ptr,
//    __CPROVER_obj_SIZE(ptr) -__CPROVER_POINTER_OFFSET(ptr));
__CPROVER_assignable_t __CPROVER_object_from(void *ptr);

// Syntactic sugar for:
// __CPROVER_obj_upto(((char *)ptr)- __CPROVER_POINTER_OFFSET(ptr),
//        __CPROVER_obj_SIZE(ptr));
__CPROVER_assignable_t  __CPROVER_whole_object(void *ptr);

// Syntactic sugar for:
// __CPROVER_obj_upto(&<expr>, sizeof(<type>));
__CPROVER_assignable_t __CPROVER_typed_target(<type> <expr>);
```

Users can specify sets of assignable locations by writing their own functions returning `__CPROVER_assignable_t.`
Such functions may call other functions returning `__CPROVER_assignable_t` (built-in or user-defined). These functions must ultimately be side-effect free, deterministic and loop-free (or they can contain loops but it must be possible to unroll these loops to termination statically at compile time).

For example, the following function defines all even cells of `arr` up to 10 as assignable:

```c
__CPROVER_assignable_t assign_even_upto_ten(int *arr, size_t size)
{
   assert(arr && size > 10);
   __CPROVER_typed_target(arr[0]);
   __CPROVER_typed_target(arr[2]);
   __CPROVER_typed_target(arr[4]);   
   __CPROVER_typed_target(arr[6]);
   __CPROVER_typed_target(arr[8]);
   __CPROVER_typed_target(arr[10]);   
}
```

This function defines a conditional set of assignable locations, and calls the previous function.

```c
__CPROVER_assignable_t my_assignable_set(int *arr, size_t size)
{
   assert(arr);
   if (0 < size)
      __CPROVER_typed_target(arr[0]);
    
   if (5 < size && size < 10)
      __CPROVER_object_upto(arr, 5*sizeof(int));
    
   if (10 < size)
      assign_even_upto_ten(arr, 5*sizeof(int));
}
```

The semantics is that, when executing the function, any call to a `__CPROVER_*` function adds the location in the assignable set.

Last, we extend the contract language to allow calls to such functions as targets in assigns clauses

```c
int foo(int *arr, size_t size)
__CPROVER_requires(!arr || __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(arr && size > 0: my_assignable_set(arr, size))
__CPROVER_ensures(true)
{ ... }

```

* * *

## Specifying freeable pointers declaratively with `__CPROVER_freeable_t`  functions in C

We provide a new built-in type meant to be used as a return type for functions that describe sets of freeable objects:

```c
typedef void `__CPROVER_freeable_t;`
```

We also provide the following built-in function:

```c
// Specify that the object pointed to by ptr may be freed
__CPROVER_freeable_t __CPROVER_freeable(void *ptr);
```

As with `__CPROVER_assignable_t` , users can write their own functions returning `__CPROVER_freeable_t`, which must be side-effect free, loop-free and deterministic.

We extend the contract language with a new clause `__CPROVER_frees` with syntax similar to that of the `__CPROVER_assigns` clause,  where we allow pointer-valued expressions and calls to functions returning `__CPROVER_freeable_t` as targets:

```c
int foo(int *arr, size_t size)
__CPROVER_requires(...)
__CPROVER_assigns(...)
__CPROVER_frees(list-of-conditional-targets)
__CPROVER_ensures(...)
{ ... }
```

We also introduce two new predicates to use in pre and post conditions:

```c
// true iff ptr is NULL or 
// points to a currently alive dynamic object and has an offset of 0
bool __CPROVER_is_freeable(void *ptr);

// true iff ptr was freed during the execution of the function(only in ensures)
bool __CPROVER_is_freed(void *ptr);

```

* * *

# Compilation of `__CPROVER_assigns` and `__CPROVER_frees` clauses to GOTO functions 
Files:
- `goto-instrument/contracts/dfcc_dsl_contract_functons.(h|cpp)`

## Generating GOTO functions from `__CPROVER_assigns` clauses

From each contract symbol `contract::foo` declaring an `assigns` clause, we generate a function in declarative style:

```c
__CPROVER_assignable_t foo::assigns(<parameter-list>);
```

The body of this function is generated from the conditional targets found in the assigns clause.

* For each target `cond: target`, where the target is an lvalue expression:

```c
DECL __cond: bool;
ASSIGN __cond = <result of goto_convert(cond)>;
IF !__cond GOTO SKIP_TARGET;
CALL __CPROVER_assignable(&target, sizeof(target), is_ptr_to_ptr(target));
SKIP_TARGET: SKIP;
DEAD __cond;
```

For each target `cond: bar(<params>)`, where `bar` is a function returning `__CPROVER_assignable_t` :

```c
DECL __cond: bool;
ASSIGN __cond = <result of goto_convert(cond)>;
IF !__cond GOTO SKIP_TARGET;
CALL bar(&target, sizeof(target));
SKIP_TARGET: SKIP;
DEAD __cond;
```
The condition expression needs to be goto_converted since it comes directly from the front-end and is allowed to contain function calls.

This function then gets translated into an active form as described in the section on instrumentation to become an active function that builds a write set and is also checked for side effects with another write set parameter.

```c
__CPROVER_assignable_t contract::foo::assigns(
 <parameter-list>,
 
 // write set to populate with new targets
 __CPROVER_contracts_write_set_ptr_t __write_set_to_fill,
 
 // write set against which to check itself for unwanted side effects
  __CPROVER_contracts_write_set_ptr_t __write_set_to_check);
```

* * *

## Generating GOTO functions from `__CPROVER_frees` clauses

We use the same approach for `frees` clauses, we generate a function

```c
__CPROVER_freeable_t contract::foo::frees(<parameter-list>);
```

* For each target `<cond>: <ptr>`:

```c
DECL __cond: bool;
ASSIGN __cond = <result of goto_convert(cond)>;
IF !__cond GOTO SKIP_TARGET;
CALL __CPROVER_freeable(<ptr>);
SKIP_TARGET: SKIP;
DEAD __cond;
```

This function then gets translated into an active form as described in the previous section to become an active function that builds a write set and is also checked for side effects with another write set parameter.

```c
__CPROVER_freeable_t contract::foo::frees(
 <parameter-list>,
 
 // write set to populate with new targets
 __CPROVER_contracts_write_set_ptr_t __write_set_to_fill,
 
 // write set against which to check itself for unwanted side effects
  __CPROVER_contracts_write_set_ptr_t __write_set_to_check);
```

* * *

# Rewriting `__CPROVER_assignable_t` functions into active DFCC functions

Files:
- `goto-instrument/contracts/dfcc_spec_functons.(h|cpp)`


User-defined functions which list assignable locations :

```c
__CPROVER_assignable_t foo(<*parameter-list>*);
```

are first inlined and checked to be loop free before being rewritten into function which accepts a write set parameter to be filled with new targets by the function:

```c
__CPROVER_assignable_t foo(
 <parameter-list>,
 
 // write set to populate with new targets
 __CPROVER_contracts_write_set_ptr_t __write_set_to_fill);
```

Calls to built in functions are numbered from 0 to N in increasing order from their position in the instruction sequence

```c
CALL __CPROVER_object_upto(ptr, size); // 0
...
CALL __CPROVER_whole_object(ptr); // 1
...
CALL __CPROVER_object_from(ptr); // 2
...
CALL __CPROVER_assignable(ptr, size, is_ptr_to_ptr); // N
```

and are rewritten into to calls to active instrumentation functions which insert into the write set

```c
CALL write_set_insert_object_upto(__write_set_to_fill, 0, ptr, size); // 0
...
CALL write_set_insert_whole_object(__write_set_to_fill, 1, ptr); // 1
...
CALL write_set_insert_object_from(__write_set_to_fill, 2, ptr); // 2
...
CALL write_set_insert_assignable(
       __write_set_to_fill, N, ptr, size, is_ptr_to_ptr); // N
```

The function then is then instrumented for side effect checking as described in [Instrumenting GOTO functions](https://quip-amazon.com/IBWxATzNHpmP#temp:C:NJW62083ab2ef5c41499c3174c1c) which augments it with a second write set parameter, intended to be the empty write set, and allows to check that the function has no unintended side effect.

```c
__CPROVER_assignable_t foo(
 <parameter-list>,
 
 // write set to populate with new targets
 __CPROVER_contracts_write_set_ptr_t __write_set_to_fill,
 
 // write set against which to check itself for unwanted side effects
  __CPROVER_contracts_write_set_ptr_t __write_set_to_check);
```

* * *

# Rewriting `__CPROVER_freeable_t` functions into active DFCC functions

Files:
- `goto-instrument/contracts/dfcc_spec_functons.(h|cpp)`


User-defined functions which list assignable locations :

```c
__CPROVER_freeable_t foo(<parameter-list>);
```

are first inlined and checked to be loop free before being rewritten into function which accepts a write set parameter to be filled with new targets by the function:

```c
__CPROVER_freeable_t foo(
 <parameter-list>,
 
 // write set to populate with new targets
 __CPROVER_contracts_write_set_ptr_t __write_set_to_fill);
```

Calls to built in function `__CPROVER_freeable`  :

```c
CALL __CPROVER_freeable(ptr); 
```

are rewritten into to calls to active instrumentation functions which insert into the write set

```c
CALL write_set_add_freeable(__write_set_to_fill, ptr); // 0
```

The function then is then instrumented for side effect checking which augments it with a second write set parameter, intended to be the empty write set, and allows to check that the function has no unintended side effect.

```c
__CPROVER_freeable_t foo(
 <parameter-list>,
 
 // write set to populate with new targets
 __CPROVER_contracts_write_set_ptr_t __write_set_to_fill,
 
 // write set against which to check itself for unwanted side effects
  __CPROVER_contracts_write_set_ptr_t __write_set_to_check);
```

* * *

# Runtime representations

The active part of the instrumentation is defined as C types and functions in the file 
- `src/ansi-c/library/cprover_contracts.c `   

and exposed in C++ by the class 
- `src/goto-instrument/contracts/dfcc_library.(h|cpp)` 

The instrumentation inserts calls to these functions in the body of the instrumented function to create dynamic write sets, update them after allocation and deallocations and perform check for assignments or side effects.

```c
/// Data type declarations for the CPROVER contracts instrumentation library

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

// A conditional address range
typedef struct __CPROVER_contracts_car_t
{
  // True iff the __CPROVER_rw_ok(lb, size) holds at creation
  __CPROVER_bool is_writable;
  // Size of the range in bytes
  __CPROVER_size_t size;
  // Lower bound
  void *lb;
  // Upper bound
  void *ub;
} __CPROVER_contracts_car_t;

// A set of car_t
typedef struct __CPROVER_contracts_car_set_t
{
  // Maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // Next usable index in elems if less than max_elems
  // (1 + greatest used index in elems)
  __CPROVER_size_t watermark;
  // An array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

// A set of pointers/pointer object IDs
typedef struct __CPROVER_contracts_obj_set_t
{
  // Maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // Next usable index in elems if less than max_elems
  // (1 + greatest used index in elems)
  __CPROVER_size_t watermark;
  // Number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // True iff nof_elems is 0
  __CPROVER_bool is_empty;
  // True iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // Array of void *pointers, indexed by their object ID if 
  // indexed_by_object_id is true, or by insertion order otherwise
  // When indexed_by_object_id is true,
  // the size of the array is set to 2^OBJECT_BITS,
  // which is the maximum value an object ID can have in SymEx. 
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

// A dynamic write set
typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording deallcations for the is_freed predicate
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif
```

```c
#ifndef CPROVER_ANSI_C_LIBRARY_CPROVER_H
#define CPROVER_ANSI_C_LIBRARY_CPROVER_H

#include "cprover_contracts_types.h"

/// Initialises a dynamic write set object
void __CPROVER_contracts_write_set_create(
  /// Pointer to the object to initialise
  __CPROVER_contracts_write_set_ptr_t set,
  /// Size of the contract's assigns clause
  __CPROVER_size_t contract_assigns_size,
  /// Size of the contract's frees clause
  __CPROVER_size_t contract_frees_size,
  /// Set to true if this is used to replace a function by its contract,
  /// false otherwise
  __CPROVER_bool replacement,
  /// Are we using this write set to check an assume-requires program ?
  __CPROVER_bool assume_requires_ctx,
  /// Are we using this write set to check an assert-requires program?
  __CPROVER_bool assert_requires_ctx,
  /// Are we using this write set to check an assume-ensures program?
  __CPROVER_bool assume_ensures_ctx,
  /// Are we using this write set to check an assert-ensures program?
  __CPROVER_bool assert_ensures_ctx);


/// Releases resources used by a write set
void __CPROVER_contracts_write_set_release(
  __CPROVER_contracts_write_set_ptr_t set);

/// Inserts a `(ptr, size)` car_t in the write set at index `idx` in
/// `set->contract_assigns`
void __CPROVER_contracts_write_set_insert_assignable(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr,
  __CPROVER_size_t size);

/// Inserts a `whole_object(ptr)` car_t in the write set at index `idx` in
/// `set->contract_assigns`
void __CPROVER_contracts_write_set_insert_whole_object(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr);

/// Inserts a `object_from(ptr)` car_t in the write set at index `idx` in
/// `set->contract_assigns`
void __CPROVER_contracts_write_set_insert_object_from(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr);

/// Inserts a `object_upto(ptr, size)` car_t in the write set at index `idx` in
/// `set->contract_assigns`
void __CPROVER_contracts_write_set_insert_object_upto(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr,
  __CPROVER_size_t size);

/// Adds a freeable pointer in `set->contract_frees`
void __CPROVER_contracts_write_set_add_freeable(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr);

/// Adds a locally DECL'd or `__CPROVER_allocate`'d object in `set->allocated`
void __CPROVER_contracts_write_set_add_allocated(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr);

/// Records a DEAD object by removing it from `set->allocated`
void __CPROVER_contracts_write_set_record_dead(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr);

/// Records a `__CPROVER_deallocate` object in `set->deallocated`
void __CPROVER_contracts_write_set_record_deallocated(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr);

/// Returns true iff the `set->deallocated` set is empty
inline __CPROVER_bool
__CPROVER_contracts_write_set_check_allocated_deallocated_is_empty(
  __CPROVER_contracts_write_set_ptr_t set);

/// Returns true iff the range `(ptr, size)` is allowed by `set`
inline __CPROVER_bool __CPROVER_contracts_write_set_check_assignment(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr,
  __CPROVER_size_t size);

/// Returns true iff a call `array_set(dest, ...)` is allowed by `set`
__CPROVER_bool __CPROVER_contracts_write_set_check_array_set(
  __CPROVER_contracts_write_set_ptr_t set,
  void *dest);

/// Returns true iff a call `array_copy(dest, ...)` is allowed by `set`
__CPROVER_bool __CPROVER_contracts_write_set_check_array_copy(
  __CPROVER_contracts_write_set_ptr_t set,
  void *dest);

/// Returns true iff a call `array_replace(dest, ...)` is allowed by `set`
__CPROVER_bool __CPROVER_contracts_write_set_check_array_replace(
  __CPROVER_contracts_write_set_ptr_t set,
  void *dest,
  void *src);

/// Returns true iff a call `havoc_object(dest, ...)` is allowed by `set`
__CPROVER_bool __CPROVER_contracts_write_set_check_havoc_object(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr);

/// Returns true iff a call `__CPROVER_deallocate(ptr)` is allowed by `set`
__CPROVER_bool __CPROVER_contracts_write_set_check_deallocate(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr);

/// Returns true iff all elements of `candidate->contract_assigns` are included
/// in some element of `reference->contract_assigns` or `reference->allocated`.
/// `candidate->allocated` must be empty.
inline __CPROVER_bool
__CPROVER_contracts_write_set_check_assigns_clause_inclusion(
  __CPROVER_contracts_write_set_ptr_t reference,
  __CPROVER_contracts_write_set_ptr_t candidate);

/// Returns true iff all elements of `candidate->contract_frees` are included
/// in some element of `reference->contract_frees` or `reference->allocated`.
/// `candidate->allocated` must be empty.
inline __CPROVER_bool
__CPROVER_contracts_write_set_check_frees_clause_inclusion(
  __CPROVER_contracts_write_set_ptr_t reference,
  __CPROVER_contracts_write_set_ptr_t candidate);

/// Non-deterministically call `__CPROVER_deallocate` on all elements of
/// `set->contract_frees`, records deallocations in `target->deallocated`.
void __CPROVER_contracts_write_set_deallocate_freeable(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_contracts_write_set_ptr_t target);

/// Links the `write_set_to_link->allocated` to
/// `write_set_postconditions->linked_allocated` so that allocations performed
/// by is_fresh predicates in post conditions are also recorded in
/// `write_set_to_link`.
void __CPROVER_contracts_link_is_fresh_allocated(
  __CPROVER_contracts_write_set_ptr_t write_set_postconditions,
  __CPROVER_contracts_write_set_ptr_t write_set_to_link);

/// Links the `write_set_to_link->deallocated` to
/// `write_set_postconditions->linked_deallocated` so that deallocations performed
/// by the function can be used by the is_freed predicates when evaluating ensures
void __CPROVER_contracts_link_deallocated(
  __CPROVER_contracts_write_set_ptr_t write_set_postconditions,
  __CPROVER_contracts_write_set_ptr_t write_set_to_link);

/// Library implementation of the is_fresh/is_freshr predicates
/// Behaviour is specialised based on the boolean flags carried by the set
/// (check vs. replace contract, requires vs. ensures clause context)
__CPROVER_bool __CPROVER_contracts_is_freshr(
  void **elem,
  __CPROVER_size_t size,
  __CPROVER_contracts_write_set_ptr_t set);

/// Returns the start address of the car at index `idx` in
/// `set->contract_assigns`.
void *__CPROVER_contracts_write_set_havoc_get_assignable_target(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx);

/// Havocs the car at index `idx` in `set->contract_assigns` with `havoc_object`
void __CPROVER_contracts_write_set_havoc_whole_object(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx);

/// Havocs the car at index `idx` in `set->contract_assigns` with `havoc_slice`
void __CPROVER_contracts_write_set_havoc_object_from(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx);

/// Havocs the car at index `idx` in `set->contract_assigns` with `havoc_slice`
void __CPROVER_contracts_write_set_havoc_object_upto(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx);

/// Returns true iff a pointer satisfies the preconditions for the `free`
/// function (pointer with offset 0 to a valid to dynamic object)
__CPROVER_bool __CPROVER_contracts_is_freeable(
  void *ptr,
  __CPROVER_contracts_write_set_ptr_t set);

/// Returns true iff the pointer is found in `set->deallocated`
__CPROVER_bool __CPROVER_contracts_is_freed(
  void *ptr,
  __CPROVER_contracts_write_set_ptr_t set);

/// Returns true iff the pointer is found in `set->contract_frees` and it is
/// hence safe to assume `__CPROVER_is_freed(ptr)` when replacing an ensures
/// clause.
void __CPROVER_contracts_check_replace_ensures_is_freed_preconditions(
  void *ptr,
  __CPROVER_contracts_write_set_ptr_t set);
```

* * *

# GOTO function instrumentation

Files:
- `goto-instrument/contracts/dfcc_instrument.(h|cpp)`

## Signature extension

Applying the DFCC instrumentation to a function turns it into a function that can be checked against a a write_set parameter. 

```c
ret_t foo(<parameters>);
```

Is turned into : 

```c
ret_t  foo( <parameters>,  __CPROVER_contracts_write_set_ptr_t write_set);
```

All instrumented checks are guarded by a null-check on the write_set pointer parameter. Passing a null pointer results in no checks being performed.

## Function body instrumentation 

### Instrumentation of DECL instructions

```
DECL x;
----
IF !write_set GOTO skip_target;
CALL add_allocated(write_set, &x);
skip_target: SKIP;
```

### Instrumentation of DEAD instructions

```
IF !write_set GOTO skip_target;
CALL record_dead(write_set, &x);
skip_target: SKIP;
----
DEAD x;
```

### Instrumentation of ASSERT instructions

Remain unchanged.

```
ASSERT <expr>;
```

### Instrumentation of ASSUME instructions

Remain unchanged.

```
ASSUME <expr>;
```

### Instrumentation of ASSIGN instructions

Assign instructions trigger checks on the LHS but also write set updates on the RHS if it represents a dynamic allocation or deallocation.

We insert write set inclusion checks for the LHS before the instruction (unless condition 1 or 2 below is met). The assigned target must be found in the `contract_assigns` set or the `allocated` set.

```
IF !write_set GOTO skip_target;
DECL check_assign: bool;
CALL check_assign = check_assignment(write_set, &lhs, sizeof(lhs));
ASSERT(check_assign);
DEAD check_assign;
skip_target: SKIP;
----
ASSIGN lhs := rhs;
```

We insert a dummy check for the instruction if:

1. the LHS is a `__CPROVER_`-prefixed symbol (these symbols are usually global variables that serve instrumentation purposes and can be understood as living in a space of their own).
2. the LHS is an expression that represents a composite access expression to a locally stack-allocated object that is not dirty (i.e. its address is never computed) or a function parameter (these are always allowed and tracked implicitly).

```
IF !write_set GOTO skip_target;
ASSERT(true, "comment describing why the assignment is always allowed");
skip_target: SKIP;
----
ASSIGN lhs := rhs;
```

If the assignment is an nondeterministic update to the `__CPROVER_dead_object`, we treat it as a dynamic deallocation. These instructions are generated to automatically cleanup objects allocated with the dynamic stack allocation function  `__builtin_alloca:`

```
ASSIGN __CPROVER_dead_object := if_exprt(nondet, ptr, dead_object);
----
IF !write_set GOTO skip_target;
CALL remove_allocated(write_set, ptr);
skip_target: SKIP;
```

If the RHS of the assignment is a `side_effect_exprt(statement = “ID_allocate)` expression, it represents a dynamic allocation and we record it in the write set:

```
CALL lhs := side_effect_exprt(statement = ID_allocate, args = {size, clear});
----
IF !write_set GOTO skip_target;
CALL add_allocated(write_set, lhs);
skip_target: SKIP;
```

### Instrumentation of CALL instructions (functions or function pointers)

If the function call is a call to the `__CPROVER_deallocate` function, it represents a dynamic deallocation and we check that the dealocated pointer is allowed by the write set, and then record the deallocation in the write set

```
IF !write_set GOTO skip_target;
DECL check_deallocate: bool;
CALL check_deallocate := check_deallocate(write_set, ptr);
ASSERT(check_deallocate);
DEAD check_deallocate;
CALL record_deallocated(write_set, lhs);
skip_target: SKIP;
----
CALL __CPROVER_deallocate(ptr);
```

For all other function calls, we proceed as follows:

If the function call has an LHS (i.e. its result is assigned to a return value variable), the LHS gets checked like for an assignment, and we pass the write set as an extra parameter to the function (remember that all functions of the goto models are extended with write_set parameters by the transformation).

```
[ // only if lhs exists
  IF !write_set GOTO skip_target;
  DECL check_assign: bool;
  CALL check_assign = check_assignment(write_set, &lhs, sizeof(lhs));
  ASSERT(check_assign);
  DEAD check_assign;
  skip_target: SKIP;
] 
----
CALL [lhs] := function(parameters, write_set);
```

### Instrumentation of OTHER instructions

`OTHER` instructions describe special built-in operations that have no explicit C or GOTO representation (they are given a semantics directly by the symex engine). From `goto_symext::symex_other` we see the possible operations are:

* `ID_expression`
* `ID_array_equal`
* `ID_array_set`
* `ID_array_copy`
* `ID_array_replace`
* `ID_havoc_object`
* `ID_decl`
* `ID_cpp_delete`
* `ID_printf`
* `code_inputt`
* `code_outputt`
* `ID_nondet`
* `ID_asm`
* `ID_user_specified_predicate`
* `ID_user_specified_parameter_predicates`
* `ID_user_specified_return_predicates`
* `ID_fence`

Remark: the instructions `code_inputt`, `code_outputt` and `ID_nondet` would also need to be instrumented as they perform side effects and introduce non-determinism, but this is not handled as of today and will trigger warnings.

For DFCC we only instrument the `array_set`, `array_copy`, `array_replace` and `havoc_object` operations. 

The example below is for `__CPROVER_array_set`, and the `dest` pointer must be found in the `contract_assigns` set or the `allocated` set.

```
IF !write_set GOTO skip_target;
DECL check_array_set: bool;
CALL check_array_set = check_array_set(write_set, dest);
ASSERT(check_array_set);
DEAD check_array_set;
skip_target: SKIP;
----
OTHER {statement = array_set, args = {dest, value}};
```

The  ranges of bytes `(void *lb, size_t size)` updated by the different operations are:

* for `array_set(dest, value)`: 
    * `lb = dest;`
    * `size = object_size(dest) - offset(ptr);`
* for `array_copy(dest, src)`
    * `lb = dest;`
    * `size =  object_size(dest) - offset(dest);`
* for `array_replace(dest, src)`
    * `lb = dest;`
    * `size =  MIN(object_size(dest) - offset(dest), size(src) - offset(src));`
* for `havoc_object(ptr)`
    * `lb = (char *)ptr - offset(ptr);`
    * `size = object_size(ptr);`


* * *

# Swapping and wrapping a function for contract checking or replacement 

Files:
- `goto-instrument/contracts/dfcc_dsl_wrapper_program.(h|cpp)`
- `goto-instrument/contracts/dfcc_contract_handler.(h|cpp)`
- `goto-instrument/contracts/dfcc_dsl_contract_handler.(h|cpp)`
- `goto-instrument/contracts/dfcc_swap_and_wrap.(h|cpp)`

We use the following swap-and-wrap technique for both contract checking and replacement.

Given a function :

```c
ret_t foo(foo_params);
```

 and a contract :

```c
ret_t contract::my_contract(contract_params);
```

We first rename `foo` and instrument it for DFCC :

```c
ret_t foo_mangled(foo_params, write_set_t caller_write_set);
```

And we regenerate a new function `foo` with the same signature which wraps the original function in a checked call or instantiates the contract behaviour for replacement (classes `dfcc_swap_and_wrap.h` and `dfcc_contract_handler.h`, `dfcc_dsl_contract_handler.h` and `dfcc_dsl_wrapper_program.h`).

```c
ret_t foo(foo_params, write_set_t caller_write_set);
```

Any function that calls `foo` now calls into the wrapper and triggers the contract checking or replacement logic.

## Contract checking

For contract checking, we generate a new function `foo` with the same interface which contains a checked call to the mangled function function or contract replacement instructions:

```c
static bool foo_check_started = false;
static bool foo_check_completed = false;

ret_t foo(foo_params, write_set_t caller_write_set) {
  assert(!foo_check_completed, "foo can only be called once from the harness");
  assert(!foo_check_started, "recursive calls to foo not allowed" );
  foo_check_started = true;
  
  // preamble
  write_set_t __contract_write_set;
  write_set_ptr_t contract_write_set;
  write_set_create(contract_write_set);
  
  // create empty write set
  // (used to check that requires/ensures have no side effects)
  write_set_t __empty_write_set;
  write_set_ptr_t empty_write_set;
  write_set_create(empty_write_set);
  
  // assume requires clauses
  assume(contract::requires(foo_params, empty_write_set));
  assume(contract::requires_contract(foo_params, empty_write_set));
  
  // snapshot history variables
  hist1 = ...;
  hist2 = ...;

  // create write set
  contract::assigns(contract_write_set, empty_write_set);
  contract::frees(contract_write_set, empty_write_set);

  // call the function
  ret_t retval = foo_mangled(foo_params, contact_write_set);
  
  // check post conditions
  assert(contract::ensures(foo_params, empty_write_set));
  assert(contract::ensures_contract(foo_params, empty_write_set));
  
  // postamble
  assert(write_set_allocated_is_empty(requires_write_set),   "no allocations in requires");
  assert(write_set_allocated_is_empty(ensures_write_set),   "no allocations in ensures");
  write_set_release(contract_write_set);
  write_set_release(requires_write_set);
  write_set_release(ensures_write_set);

  foo_check_completed = true;

  return retval;
}

```

## Contract replacement

For contract replacement, we generate a new function `foo` with the same interface which contains instructions modelling the nondeterministic contract behaviour (class `dfcc_dsl_wrapper_program.h`):


```c
ret_t foo(foo_params, write_set_t caller_write_set) {

    // preamble
    write_set_t __contract_write_set;
    write_set_ptr_t contract_write_set;
    write_set_create(contract_write_set);
    
    // create empty write set
    // (used to check that requires/ensures have no side effects)
    write_set_t __requires_write_set;
    write_set_ptr_t requires_write_set;
    write_set_create(requires_write_set);

    write_set_t __ensures_write_set;
    write_set_ptr_t ensures_write_set;
    write_set_create(ensures_write_set);
    
    // assume requires clauses
    assert(contract::requires(foo_params, requires_write_set));
    assert(contract::requires_contract(foo_params, requires_write_set));
    
    // snapshot history variables
    hist1 = ...;
    hist2 = ...;

    // create write set
    contract::assigns(contract_write_set, empty_write_set);
    contract::frees(contract_write_set, empty_write_set);
    
    // check inclusion with caller
    assert(write_set_check_inclusion(caller_write_set, contract_write_set));
    
    // havoc state
    write_set_havoc(contract_write_set);
    ret_t retval = nondet();
    
    // free freeable pointers
    write_set_nondet_free_freeable(contract_write_set);
    
    // link caller write set and write set so that allocations due to is_fresh
    // in post conditions are recorded in the caller write set
    write_set_link_allocated(caller_write_set, ensures_write_set);

   // link the ensures write set to the contract write set so that the is_freed predicates in the postconditions
   // get access to the deallocated pointers
    write_set_link_deallocated(ensures_write_set, contract_write_set);
    
    // assume post conditions
    assume(contract::ensures(foo_params, ensures_write_set));
    assume(contract::ensures_contract(foo_params, ensures_write_set));
    
    // postamble
    assert(write_set_is_empty(requires_write_set));
    assert(write_set_is_empty(ensures_write_set));
    write_set_release(contract_write_set);
    write_set_release(requires_write_set);
    write_set_release(ensures_write_set);

    return retval;  
}

```

## Contract checking for recursive functions

If a function is potentially recursive, we generate the wrapper function body such that the first call trigger the contract checking, and any subsequent call triggers the contract replacement logic 


```c
static bool foo_check_started = false;
static bool foo_check_completed = false;

ret_t foo(foo_params, write_set_t caller_write_set) {
  assert(!foo_check_completed, "foo can only be called once from the harness");
  
   // first call, check the contract
  if(!foo_check_started) {
    assert(!foo_check_completed, "foo can only be called once from the harness");
    foo_check_started = true;
    <contract checking instructions as described above>
    foo_check_completed = true;
   return retval;
  } else {
    <contract replacement instructions as described above>
   return retval;
  }
}
```

* * *

# Harness function instrumentation

Files:
-  `src/goto-instrument/contracts/dfcc_instrument.(h|cpp)`

The harness function is the entry point of the analysis and is meant to contain a direct or indirect call to the function being checked against a contract or potentially several functions replaced by contracts. The harness can also contain preamble instructions to set up proof assumptions or perform cleanup after the call to the checked function. We do not want to check these functions and instructions against any particular write set.  Instrumenting a harness function just consists in passing a NULL value for the write_set parameter to all function and function pointer calls it contains. This will result in no write_set updates or checks being performed in the harness or in the functions called directly from the harness (and transitively in functions they call). One of the functions called directly (or indirectly) by the harness is eventually going to be a wrapper function that checks the contract against the function of interest. This wrapper will ignore the NULL write set it received from the harness and instantiate its own local write set from the contract and pass it to the function under analysis. This will trigger cascading checks in all functions called from the checked function thanks to the propagation of the write set through function calls and function pointer calls.

* * *

# `__CPROVER_is_fresh` and `__CPROVER_is_freshr` predicates

Files:
-  `src/ansi-c/library/cprover_contracts.c`
-  `src/goto-instrument/contracts/dfcc_is_fresh.(h|cpp)`

In goto programs encoding pre or post conditions (generated from the contract clauses) and in all user-defined functions, we simply replace calls to `__CPROVER_is_fresh` and `__CPROVER_is_fresh` with calls to the library implementation

```
__CPROVER_contracts_is_freshr(void **ptr, size_t size, __CPROVER_contracts_write_set_ptr_t write_set);
```

This function implements the is_fresh behaviour in all possible contexts (contract checking vs replacement, requires vs ensures clause context), and receives the context information from the write set it receives as parameter. The context flags are set on the write set upon creation depending on the context.

# `__CPROVER_is_freeable` and `__CPROVER_is_freed` predicates

Files:
-  `src/ansi-c/library/cprover_contracts.c`
-  `src/goto-instrument/contracts/dfcc_is_freeable.(h|cpp)`

In goto programs encoding pre or post conditions (generated from the contract clauses) and in all user-defined functions, we simply replace calls to `__CPROVER_is_freeable` with a calls to its library implementation:

```
__CPROVER_contracts_is_freeable(void *ptr, __CPROVER_contracts_write_set_ptr_t write_set);
```

The behaviour of `__CPROVER_contracts_is_freeable` can only be used in requires clauses, and it needs to use a weaker definition when used in assumption contexts (contract checking vs replacement). Context flags are obtained from the write set instance an interpreted by the library function.

For `__CPROVER_is_freed`, which can only be used in post conditions, we also map calls to a library implementation:

```
__CPROVER_contracts_is_freed(void *ptr, __CPROVER_contracts_write_set_ptr_t write_set);
```
This function performs a lookup in the `write_set->deallocated` pointer set to check if the function under analysis indeed deallocated the object. The result of this check will then be either asserted for contract checking or assumed for contract replacement. on the context. When turned in an assumption, we instantiate an extra assertion before the assumption, in order to check that the pointer is in always found in the freeable set of the contract and that it is safe to assume it is freed, without causing an immediate contradiction.
