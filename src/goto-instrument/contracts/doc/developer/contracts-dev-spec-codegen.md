# Generating GOTO Functions From Contract Clauses {#contracts-dev-spec-codegen}

Back to top @ref contracts-dev-spec

@tableofcontents

## Translating Assigns Clauses to GOTO Functions {#contracts-dev-spec-codegen-assigns}


Let's consider a contract `foo` (with corresponding pure contract
`contract::foo`) with a `__CPROVER_assigns(A)` clause.

```c
ret_t foo(foo-parameters) __CPROVER_assigns(A);
```
We know the elements of A only depend on `foo-parameters` and global variables.

A new GOTO function with the following signature is generated:

```c
void contract::foo::assigns(foo-parameters);
```

The body of the function generated from the elements of A as follows:
- For each target `cond: target` where the target is an lvalue expression:
    ```c
    DECL __cond: bool;
    ASSIGN __cond = <result of goto_convert(cond)>;
    IF !__cond GOTO SKIP_TARGET;
    CALL __CPROVER_assignable(&target, sizeof(target), has_ptr_type(target));
    SKIP_TARGET: SKIP;
    DEAD __cond;
    ```
    where `has_ptr_type(target)` returns true if the target has a pointer-type;
- For each target `cond: f(parameters)`, where `f` is a void-typed function:
    ```c
    DECL __cond: bool;
    ASSIGN __cond = <result of goto_convert(cond)>;
    IF !__cond GOTO SKIP_TARGET;
    CALL f(parameters);
    SKIP_TARGET: SKIP;
    DEAD __cond;
    ```

Remark: The condition expressions needs to be goto_converted during translation
since they come directly from the front-end and are allowed to contain function
calls.

The rewriting pass @ref contracts-dev-spec-spec-rewriting-assigns is applied
to transform the function into a function that accepts two
write set parameters: The first one is the write set that gets populated with
assignable locations specified by the function, the second is a write set that
is used by the function to check its side effects.

```c
void contract::foo::assigns(

  // function parameters
  foo-parameters,

  // write set to populate with new targets
  __CPROVER_contracts_write_set_ptr_t __write_set_to_fill,

  // write set against which to check itself for unwanted side effects
  __CPROVER_contracts_write_set_ptr_t __write_set_to_check);
```

The rewriting step @ref contracts-dev-spec-spec-rewriting-havoc is also applied
to the function in order to generate a havoc function that can be used to model
contract replacement:

```c
void contract::foo::havoc(__CPROVER_contracts_write_set_ptr_t __write_set_to_havoc);
```

## Translating Frees Clauses to GOTO Functions {#contracts-dev-spec-codegen-frees}

Let's consider a contract `foo` (with corresponding pure contract
`contract::foo`) with a `__CPROVER_frees(F)` clause.

```c
ret_t foo(foo-parameters) __CPROVER_frees(F);
```
We know the elements of F only depend on `foo-parameters` and global variables.

A new GOTO function with the following signature is generated:

```c
void contract::foo::frees(foo-parameters);
```

The body of the function generated from the elements of F as follows:
- For each element of the form  `cond: expr` where `expr` is a pointer-typed
  expression:
    ```c
    DECL __cond: bool;
    ASSIGN __cond = <result of goto_convert(cond)>;
    IF !__cond GOTO SKIP_TARGET;
    CALL __CPROVER_freeable(expr);
    SKIP_TARGET: SKIP;
    DEAD __cond;
    ```
- For each target of the form `cond: f(params)` where `f` is a void-typed
  function:
    ```c
    DECL __cond: bool;
    ASSIGN __cond = <result of goto_convert(cond)>;
    IF !__cond GOTO SKIP_TARGET;
    CALL f(params);
    SKIP_TARGET: SKIP;
    DEAD __cond;
    ```

Remark: The condition expressions needs to be goto_converted during translation
since they come directly from the front-end and are allowed to contain function
calls.

The resulting function is declarative, in the sense that it describes the
contents of the frees clause but does not have any runtime effects.

The rewriting pass @ref contracts-dev-spec-spec-rewriting-frees is applied
to transform the function into a function that accepts two
write set parameters: The first one is the write set that gets populated with
freeable pointers specified by the function, the second is a write set that is
used by the function to check its side effects.

```c
void contract::foo::frees(

  // function parameters
  foo-parameters,

  // write set to populate with new targets
  __CPROVER_contracts_write_set_ptr_t __write_set_to_fill,

  // write set against which to check itself for unwanted side effects
  __CPROVER_contracts_write_set_ptr_t __write_set_to_check);
```

---
 Prev | Next
:-----|:------
 @ref contracts-dev-spec-transform-params | @ref contracts-dev-spec-spec-rewriting