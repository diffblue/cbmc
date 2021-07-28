# History Variables

### Syntax

```c
__CPROVER_old(*identifier*)
```

Refers to the value of a given object in the pre-state of a function within the
_ensures_ clause.

**Important.** This function may be used only within the context of `__CPROVER_ensures`.

### Parameters

`__CPROVER_old` takes a single argument, which is the identifier corresponding to
a parameter of the function. For now, only scalar or pointer types are supported.

### Semantics

To illustrate the behavior of `__CPROVER_old`, take a look at the example
bellow.  If the function returns a failure code, the value of `*out` should not
have been modified.

```c
int sum(const uint32_t a, const uint32_t b, uint32_t* out)
/* Postconditions */
__CPROVER_ensures((__CPROVER_return_value == FAILURE) ==> (*out == __CPROVER_old(*out)))
/* Writable Set */
__CPROVER_assigns(*out)
{
  /* ... */
}
```
