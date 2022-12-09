# GOTO Function Instrumentation {#contracts-dev-spec-dfcc-instrument}

Back to top @ref contracts-dev-spec

@tableofcontents

Applying the DFCC instrumentation to a function turns it into a function that
can be checked against a write set passed as parameter.

## Signature Extension {#contracts-dev-spec-dfcc-instrument-signature}

The signature of a function:

```c
ret_t foo(foo-parameters);
```

is turned into the extended version:

```c
ret_t  foo(foo-parameters,  __CPROVER_contracts_write_set_ptr_t write_set);
```

After this step the `write_set` parameter is in scope in the function and can
be used to implement checks.

It is valid to pass a `NULL` pointer for the `write_set` parameter. When the
`write_set` parameter is NULL, no checks are performed in the function.

## Body Instrumentation {#contracts-dev-spec-dfcc-instrument-body}

Body instrumentation inserts additional goto instructions in the function's
GOTO instruction sequence.

All instrumented checks are guarded by a null-check on the `write_set`
pointer parameter. Hence, passing a `NULL` pointer results in no checks being
performed in the function.

### Instrumenting DECL Instructions

```c
DECL x;
----
IF !write_set GOTO skip_target;
CALL __CPROVER_contract_write_set_add_allocated(write_set, &x);
skip_target: SKIP;
```

### Instrumenting DEAD Instructions

```c
IF !write_set GOTO skip_target;
CALL __CPROVER_contract_write_set_record_dead(write_set, &x);
skip_target: SKIP;
----
DEAD x;
```

### Instrumenting ASSERT Instructions

No instrumentation is performed.

```c
ASSERT expr;
```

### Instrumenting ASSUME Instructions

No instrumentation is performed.

```c
ASSUME expr;
```

### Instrumenting ASSIGN Instructions

Assign instructions trigger a check on the LHS but also triggers an update of
the write set if the RHS if it represents a dynamic allocation or deallocation.

#### LHS Instrumentation

Checks are inserted before the instruction.

If the LHS is either:
- a `__CPROVER_`-prefixed symbol (these symbols are usually global variables
  that serve instrumentation purposes and can be understood as living in a
  namespace of their own)
- an expression that represents a composite access expression to a locally
  stack-allocated object that is not dirty (i.e. its address is never computed)
  or a to a function parameter (these are always implicitly allowed)

Then no check is performed, i.e. `ASSERT true;` is inserted:

```c
IF !write_set GOTO skip_target;
ASSERT(true, "comment describing why the assignment is always allowed");
skip_target: SKIP;
----
ASSIGN lhs := rhs;
```

Otherwise, we check that the LHS is found in the write set's `contract_assigns`
set or the `allocated` set as shown below:

```c
IF !write_set GOTO skip_target;
DECL check_assign: bool;
CALL check_assign =
  __CPROVER_contracts_write_set_check_assignment(
    write_set, &lhs, sizeof(lhs));
ASSERT check_assign;
DEAD check_assign;
skip_target: SKIP;
----
ASSIGN lhs := rhs;
```

#### RHS Instrumentation

For the write set updates we consider the following cases.

If the RHS of the assignment is a `side_effect_exprt(statement = ID_allocate)`
expression, it represents a dynamic allocation. We record it in the write set:

```c
CALL lhs := side_effect_exprt(statement = ID_allocate, args = {size, clear});
----
IF !write_set GOTO skip_target;
CALL __CPROVER_contracts_write_set_add_allocated(write_set, lhs);
skip_target: SKIP;
```

If the assignment is an nondeterministic update to the `__CPROVER_dead_object`,
it in fact models a dynamic deallocation. Such instructions are generated to
deallocate objects allocated with the dynamic stack allocation function
`__builtin_alloca` and are always legal. We just record the deallocation.

```c
ASSIGN __CPROVER_dead_object := if_exprt(nondet, ptr, dead_object);
----
IF !write_set GOTO skip_target;
CALL __CPROVER_contracts_write_set_record_deallocated(write_set, ptr);
skip_target: SKIP;
```

### Instrumenting CALL Instructions

If the function call is a call to the `__CPROVER_deallocate` function,
it represents a dynamic deallocation and we check that the deallocated pointer
is allowed by the write set, and then record the deallocation in the write set.

```c
IF !write_set GOTO skip_target;
DECL check_deallocate: bool;
CALL check_deallocate :=
 __CPROVER_contracts_write_set_check_deallocate(write_set, ptr);
ASSERT(check_deallocate);
DEAD check_deallocate;
CALL __CPROVER_contracts_write_set_record_deallocated(write_set, lhs);
skip_target: SKIP;
----
CALL __CPROVER_deallocate(ptr);
```

Calls to `__CPROVER_was_freed` or `__CPROVER_is_freeable` are rewritten as
described in @subpage contracts-dev-spec-is-freeable

Calls to `__CPROVER_is_fresh` are rewritten as described in
@subpage contracts-dev-spec-is-fresh

Calls to `__CPROVER_obeys_contract` are rewritten as described in
@subpage contracts-dev-spec-obeys-contract

Calls to `__CPROVER_pointer_in_range_dfcc` are rewritten as described in
@subpage contracts-dev-spec-pointer-in-range

For all other function or function pointer calls, we proceed as follows.

If the function call has an LHS (i.e. its result is assigned to a return value
variable), the LHS gets checked like for an assignment, and we pass the write
set as an extra parameter to the function (remember that all functions of the
goto models are extended with write_set parameters by the transformation).

```c
// If the LHS exists
IF !write_set GOTO skip_target;
DECL check_assign: bool;
CALL check_assign =
__CPROVER_contracts_write_set_check_assignment(write_set, &lhs, sizeof(lhs));
ASSERT(check_assign);
DEAD check_assign;
skip_target: SKIP;
----
CALL [lhs] := function(parameters, write_set);
```

### Instrumenting OTHER Instructions

`OTHER` instructions describe special built-in operations that have no explicit
C or GOTO representation (they are given a semantics directly by the symex
engine). From `goto_symext::symex_other` we see the possible operations are:

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

Remark: the instructions `code_inputt`, `code_outputt` and `ID_nondet` would
also need to be instrumented as they perform side effects and introduce
non-determinism, but this is not handled as of today and will trigger warnings.

For DFCC we only instrument the `array_set`, `array_copy`, `array_replace` and
`havoc_object` operations.

The example below is for `__CPROVER_array_set`, and the `dest` pointer must be
found in the `contract_assigns` set or the `allocated` set.

```c
IF !write_set GOTO skip_target;
DECL check_array_set: bool;
CALL check_array_set = 
 __CPROVER_contracts_write_set_check_array_set(write_set, dest);
ASSERT(check_array_set);
DEAD check_array_set;
skip_target: SKIP;
----
OTHER {statement = array_set, args = {dest, value}};
```

The  ranges of bytes `(void *lb, size_t size)` updated by the different operations are:

* for `array_set(dest, value)`:
    * `lb = dest;`
    * `size = object_size(dest) - pointer_offset(ptr);`
* for `array_copy(dest, src)`
    * `lb = dest;`
    * `size =  object_size(dest) - pointer_offset(dest);`
* for `array_replace(dest, src)`
    * `lb = dest;`
    * `size =  MIN(object_size(dest) - pointer_offset(dest), object_size(src) - pointer_offset(src));`
* for `havoc_object(ptr)`
    * `lb = (char *)ptr - pointer_offset(ptr);`
    * `size = object_size(ptr);`

---
 Prev | Next
:-----|:------
 @ref contracts-dev-spec-dfcc | @ref contracts-dev-spec-harness