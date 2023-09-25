# Shadow Memory

The Symbolic Shadow Memory module described below is an implementation of
what is outlined in the paper [CBMC-SSM: Bounded Model Checking of C Programs
with Symbolic Shadow Memory](https://dl.acm.org/doi/abs/10.1145/3551349.3559523).

## Introduction

CBMC implements *Symbolic Shadow Memory*. Symbolic Shadow Memory (from now on,
SSM) allows one to create a parallel memory structure that is maintained by the
analysis program and that shadows the standard memory of the program. In the
Shadow Memory structure, a user can create fields, for which he can get
(retrieve) and set values.

By doing so, a user can organise their own tracking of metadata related to the
code, in a way that is then considered by the backend of CBMC during analysis.
This can be used to implement novel analyses that the CBMC framework itself does
not support. For example, the paper above presents as an example a taint
analysis implemented with the use of the SSM component described here.

## Usage

A user can interact with the Symbolic Shadow Memory component through four CBMC
primitives. These allow the declaration of shadow memory fields, and get/set
their corresponding values:

* `__CPROVER_field_decl_local`
* `__CPROVER_field_decl_global`
* `__CPROVER_get_field`
* `__CPROVER_set_field`

More precisely, their signatures (in pseudo-C, because of some constraints that
we cannot express using the type system), along with some small examples of their
usage, are described below:

### `void __CPROVER_field_decl_local(type1 field_name, SSM_value_type init_value)`

Type constraints:

* `type1`: string literal, such as `"field"`,
* `SSM_value_type`: any value up to 8 bits in size (signed or unsigned).

Declares a local shadow memory field called `field_name`, and initialises it
with the value `init_value`. The field is going to be associated with
function local-scope objects (i.e. a variable on the stack).

Note that each function scope will have a separate *local* shadow memory, so the
value stored in the *local* shadow memory is not propagated to subcalls (even
when the call is recursive). For this reason, to be able to access shadow memory
argument values from a called function or the value of the return from the
callee it is necessary to use the global shadow memory and passing arguments and
return values as pointers or to use global variables.

```c
void func() {
    // Sample local object (local variable)
    char x = 0;
    
    // Shadow memory field associated with local objects.
    __CPROVER_field_decl_local("shadow", (_Bool)1);
}
```

### `void __CPROVER_field_decl_global(type1 field_name, SSM_value_type init_value)`

Type constraints:

* `type1`: string literal, such as `"field"`,
* `SSM_value_type`: any value up to 8 bits in size (signed or unsigned).

As for `__CPROVER_field_decl_local`, but the field declared is associated with
objects whose lifetime exceeds the current function scope (i.e. global variables
or heap allocated objects).

```c
// Sample global object
int a = 10;

void func() {
    // Shadow memory field associated with global objects.
    __CPROVER_field_decl_global("shadow", (_Bool)0);
}
```

### `SSM_VALUE_TYPE __CPROVER_get_field(type1 *p, type2 field_name)`

Type constraints:

* `SSM_VALUE_TYPE`: the type of the returned value is the same of the SSM field,
   i.e. the type that was used to intialise the SSM field during declaration,
* `type1 *`: a non-`void` pointer to an object of type `type1`, whose address we
   are going to use for indexing the shadow memory component for the field
   declared,
* `type2`: a string literal-typed value, denoting the name of the field whose
   value we want to retrieve, such as `"field"`.

Retrieves the latest value associated with a SSM field to the given pointer.
This would be either the value the field was declared to be initialised with,
or, if there had been subsequent changes to it through a `__CPROVER_set_field`
(see `__CPROVER_set_field` section below), the value that it was last `set`
with.

```c
// Sample global object
int a = 10;

void func() {
    // Shadow memory field (called "field") associated with global objects.
    __CPROVER_field_decl_global("shadow", (_Bool)0);

    _Bool shadow_x = __CPROVER_get_field(&a, "shadow");
    __CPROVER_assert(shadow_x == 0, "expected success: field initialised with 0");
    __CPROVER_assert(shadow_x == 1, "expected fail: field initialised with 0");
}
```

Note that getting the value of a local variable from a global SSM field or the
opposite will return the default value for that SSM field (and it **will not**
fail).

### `void __CPROVER_set_field(type1 *p, type2 field_name, type3 set_value)`

Type constraints:

* `type1 *`: a non-`void` pointer to an object of type `type1`, whose address we
   are going to use for indexing the shadow memory component for the field
   declared,
* `type2`: a string literal-typed value, denoting the name of the field whose
   value we want to retrieve, such as `"field"`,
* `type3`: type of the value to be set. This can be any integer type signed or
   unsigned (including `_Bool`). Notice that if this type differs from the type
   the SSM field was declared with (`SSM_VALUE_TYPE` above) it will be
   implicitly casted to it.

Sets the value associated with a SSM field to the given pointer `p` with the
given value `set_value`. If the `set_value` type is not the `SSM_VALUE_TYPE`, it
will be implicitly casted to it.

```c
// Sample global object, used for addressing within the SSM component.
int a = 10;

void func() {
    // Shadow memory field (called "field") associated with global objects.
    // Originally assigned a value of `0`, of type `_Bool`.
    __CPROVER_field_decl_global("shadow", (_Bool)0);

    // Retrieve the value of the field named "shadow" associated with the address
    // of the object `a`. 
    _Bool shadow_x = __CPROVER_get_field(&a, "shadow");
    __CPROVER_assert(shadow_x == 0, "expected success: field defaulted to a value of 0");

    // Set field "shadow" for the memory location denoted by the address of `a`
    // to a value of `1`.
    __CPROVER_set_field(&a, "shadow", 1);
    // Retrieve the value of the field named "shadow" associated with the address
    // of the object `a`.
    shadow_x = __CPROVER_get_field(&a, "shadow");
    __CPROVER_assert(shadow_x == 1, "expected success: field set to a value of 1");
}
```

Note that setting the value of a local variable from a global SSM field or the
opposite will produce no effect (and it **will not** fail).

### Working with Compound Type Objects

When using SSM on compound type pointers (e.g. `struct` and `union`) the value
used for the `__CPROVER_set_field` will be replicated in each of the fields of
the type, and aggregated again when retrieving them with `__CPROVER_get_field`.
The aggregation function is `or` for an SSM field of `_Bool` type, and `max` for
other types.

This is helpful, for example, in the case of taint analysis (as presented in the
paper and shown below). In this case, when retrieving the taint value of a
struct containing a tainted field the result value will indicate taint (without
the need for changing non-tainted field values), and when setting the taint
value of a struct then all its fields will be set to the given value.

```c
struct S {
  unsigned long f1;
  char f2;
};

void func() {
  // Shadow memory field (called "field") associated with local objects.
  // Originally assigned a value of `0`, of type `_Bool`.
  __CPROVER_field_decl_local("shadow", (_Bool)0);

  // Struct typed variable
  struct S s;
  
  // Retrieve the value of the field named "shadow" associated with the address
  // of the object `s`. Here we expect a `0` as default.
  __CPROVER_assert(__CPROVER_get_field(&s, "shadow") == 0, 
                   "expected success: field defaulted to a value of 0");
  // Retrieve the value of the field named "shadow" associated with the address
  // of the field `f1` of the object `s`. Here we expect a `0` as default.
  __CPROVER_assert(__CPROVER_get_field(&s.f1, "shadow") == 0, 
                   "expected success: field defaulted to a value of 0");
  // Retrieve the value of the field named "shadow" associated with the address
  // of the field `f1` of the object `s`. Here we expect a `0` as default.
  __CPROVER_assert(__CPROVER_get_field(&s.f2, "shadow") == 0, 
                   "expected success: field defaulted to a value of 0");


  // Set the shadow memory of the field `f1` (ONLY) of the object `s`.
  __CPROVER_set_field(&s.f1, "shadow", 1);

  // Retrieve the value of the field named "shadow" associated with the address
  // of the object `s`. Here we expect a `1` as the value of field `f1` (after
  // aggregating all its field values using `max`).
  __CPROVER_assert(__CPROVER_get_field(&s, "shadow") == 1, 
                   "expected success: field previously set to a value of 1");
  // Retrieve the value of the field named "shadow" associated with the address
  // of the field `f1` of the object `s`. Here we expect a `1` as set above.
  __CPROVER_assert(__CPROVER_get_field(&s.f1, "shadow") == 1, 
                   "expected success: field previously set to a value of 1");
  // Retrieve the value of the field named "shadow" associated with the address
  // of the field `f2` of the object `s`. Here we expect a `0` as default.
  __CPROVER_assert(__CPROVER_get_field(&s.f2, "shadow") == 0, 
                   "expected success: field defaulted to a value of 0");


  // Set the shadow memory of the object `s`. This in turns sets also the 
  // values of each (shadow) field of `s`.
  __CPROVER_set_field(&s, "shadow", 0);

  // Retrieve the value of the field named "shadow" associated with the address
  // of the object `s`. Here we expect a `0` as set above.
  __CPROVER_assert(__CPROVER_get_field(&s, "shadow") == 0, 
                   "expected success: field previously set to a value of 0");
  // Retrieve the value of the field named "shadow" associated with the address
  // of the field `f1` of the object `s`. Here we expect a `0` as the set
  // above was replicated on all the fields of `s`.
  __CPROVER_assert(__CPROVER_get_field(&s.f1, "shadow") == 0, 
                   "expected success: field previously set to a value of 0");
  // Retrieve the value of the field named "shadow" associated with the address
  // of the field `f2` of the object `s`. Here we expect a `0` as the set
  // above was replicated on all the fields of `s`.
  __CPROVER_assert(__CPROVER_get_field(&s.f2, "shadow") == 0, 
                   "expected success: field previously set to a value of 0");
}
```


