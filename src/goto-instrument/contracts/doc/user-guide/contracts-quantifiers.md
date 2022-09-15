[CPROVER Manual TOC](../../)

# Quantifiers

### Syntax

```c
__CPROVER_forall { *type* *identifier*; *boolean expression* }
__CPROVER_exists { *type* *identifier*; *boolean expression* }
```

While quantified expressions with arbitrary Boolean expressions are supported with an SMT backend, the SAT backend only supports bounded quantification under _constant_ lower & upper bounds. This is because the SAT backend currently expands a universal quantifier (`__CPROVER_forall`) to a conjunction and an existential quantifier (`__CPROVER_exists`) to a disjunction on each value within the specified bound.

Concretely, with the SAT backend, the following syntax must be used for quantifiers:

```
__CPROVER_forall { *id* *type*; *range* => *boolean expression* }
__CPROVER_exists { *id* *type*; *range* && *boolean expression* }
```

where `*range*` is an expression of the form

```
*lower bound* <= *id* && *id* < *upper bound*
```

where `*lower bound*`and `*upper bound*` are constants.
The bound predicates could be strict (e.g., `*lower bound* < *id*`),
or non-strict (e.g., `*upper bound* <= *id*`),
but both the bounds **must** be constants.


### Semantics

For `__CPROVER_forall` all `*type*` values for `*identifier*` must satisfy
`*boolean expression*`.

```c
int foo(int *arr, int len)
  /* ... */
  __CPROVER_ensures(__CPROVER_forall {
    int i;
    (0 <= i && i < len) ==> arr[i] == 0
  })
{
  /* every element in arr must be set to 0 */
}
```

For `__CPROVER_exists` some (at least one) `*type*` value for `*identifier*`
must satisfy `*boolean expression*`.

```c
int bar(int *arr, int len)
  __CPROVER_requires(__CPROVER_exists {
    int i;
    (0 <= i && i < len) && arr[i] == 1
  })
  /* ... */
{
  /* at least one element in arr must be set to 1 */
}
```

The examples above only work with the SMT backend, since `len` is not constant.
However, if a constant maximum upper bound, say `MAX_LEN`, is known,
then the following workaround may be used with the SAT backend:

```c
int foo_sat(int *arr, int len)
  /* ... */
  __CPROVER_ensures(__CPROVER_forall {
    int i;
    (0 <= i && i < MAX_LEN) ==>
      (i < len ==> arr[i] == 0)
  })
{
  /* every element in arr must be set to 0 */
}

int bar_sat(int *arr, int len)
  __CPROVER_requires(__CPROVER_exists {
    int i;
    (0 <= i && i < MAX_LEN) &&
      (i < len && arr[i] == 1)
  })
  /* ... */
{
  /* at least one element in arr must be set to 1 */
}
```
