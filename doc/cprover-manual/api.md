[CPROVER Manual TOC](../)

## The CPROVER API Reference

The following sections summarize the functions available to programs
that are passed to the CPROVER tools.

### Functions

#### \_\_CPROVER\_assume, \_\_CPROVER\_assert, assert

```C
void __CPROVER_assume(_Bool assumption);
void __CPROVER_assert(_Bool assertion, const char *description);
void assert(_Bool assertion);
```

The function **\_\_CPROVER\_assume** adds an expression as a constraint
to the program. If the expression evaluates to false, the execution
aborts without failure. More detail on the use of assumptions is in the
section on [Assumptions](../modeling/assumptions/).

#### \_\_CPROVER\_r_ok, \_\_CPROVER\_w_ok

```C
void __CPROVER_r_ok(const void *, size_t size);
void __CPROVER_w_ok(const void *, size_t size);
```

The function **\_\_CPROVER\_r_ok** returns true if reading the piece of
memory starting at the given pointer with the given size is safe.
**\_\_CPROVER\_w_ok** does the same with writing.

#### \_\_CPROVER\_same\_object, \_\_CPROVER\_POINTER\_OBJECT, \_\_CPROVER\_POINTER\_OFFSET, \_\_CPROVER\_DYNAMIC\_OBJECT

```C
_Bool __CPROVER_same_object(const void *, const void *);
__CPROVER_size_t __CPROVER_POINTER_OBJECT(const void *p);
__CPROVER_ssize_t __CPROVER_POINTER_OFFSET(const void *p);
_Bool __CPROVER_DYNAMIC_OBJECT(const void *p);
```

The function **\_\_CPROVER\_same\_object** returns true if the two
pointers given as arguments point to the same object. The function
**\_\_CPROVER\_POINTER\_OFFSET** returns the offset of the given pointer
relative to the base address of the object. The function
**\_\_CPROVER\_DYNAMIC\_OBJECT** returns true if the pointer passed as
arguments points to a dynamically allocated object.

#### \_\_CPROVER\_is\_zero\_string, \_\_CPROVER\_zero\_string\_length, \_\_CPROVER\_buffer\_size

```C
_Bool __CPROVER_is_zero_string(const void *);
__CPROVER_size_t __CPROVER_zero_string_length(const void *);
__CPROVER_size_t __CPROVER_buffer_size(const void *);
```

#### \_\_CPROVER\_initialize

```C
void __CPROVER_initialize(void);
```

The function **\_\_CPROVER\_initialize** computes the initial state of
the program. It is called prior to calling the main procedure of the
program.

#### \_\_CPROVER\_input, \_\_CPROVER\_output

```C
void __CPROVER_input(const char *id, ...);
void __CPROVER_output(const char *id, ...);
```

The functions **\_\_CPROVER\_input** and **\_\_CPROVER\_output** are
used to report an input or output value. Note that they do not generate
input or output values. The first argument is a string constant to
distinguish multiple inputs and outputs (inputs are typically generated
using nondeterminism, as described [here](../modeling/nondeterminism/)). The
string constant is followed by an arbitrary number of values of
arbitrary types.

#### \_\_CPROVER\_cover

```C
void __CPROVER_cover(_Bool condition);
```

This statement defines a custom coverage criterion, for usage with the
[test suite generation feature](cover.shtml).

#### \_\_CPROVER\_isnan, \_\_CPROVER\_isfinite, \_\_CPROVER\_isinf, \_\_CPROVER\_isnormal, \_\_CPROVER\_sign

```C
_Bool __CPROVER_isnan(double f);
_Bool __CPROVER_isfinite(double f);
_Bool __CPROVER_isinf(double f);
_Bool __CPROVER_isnormal(double f);
_Bool __CPROVER_sign(double f);
```

The function **\_\_CPROVER\_isnan** returns true if the double-precision
floating-point number passed as argument is a
[NaN](http://en.wikipedia.org/wiki/NaN).

The function **\_\_CPROVER\_isfinite** returns true if the
double-precision floating-point number passed as argument is a finite
number.

This function **\_\_CPROVER\_isinf** returns true if the
double-precision floating-point number passed as argument is plus or
minus infinity.

The function **\_\_CPROVER\_isnormal** returns true if the
double-precision floating-point number passed as argument is a normal
number.

This function **\_\_CPROVER\_sign** returns true if the double-precision
floating-point number passed as argument is negative.

#### \_\_CPROVER\_abs, \_\_CPROVER\_labs, \_\_CPROVER\_fabs, \_\_CPROVER\_fabsl, \_\_CPROVER\_fabsf

```C
int __CPROVER_abs(int x);
long int __CPROVER_labs(long int x);
double __CPROVER_fabs(double x);
long double __CPROVER_fabsl(long double x);
float __CPROVER_fabsf(float x);
```

These functions return the absolute value of the given argument.

#### \_\_CPROVER\_array\_equal, \_\_CPROVER\_array\_copy, \_\_CPROVER\_array\_set

```C
_Bool __CPROVER_array_equal(const void array1[], const void array2[]);
void __CPROVER_array_copy(const void dest[], const void src[]);
void __CPROVER_array_set(const void dest[], value);
```

The function **\_\_CPROVER\_array\_equal** returns true if the values
stored in the given arrays are equal. The function
**\_\_CPROVER\_array\_copy** copies the contents of the array **src** to
the array **dest**. The function **\_\_CPROVER\_array\_set** initializes
the array **dest** with the given value.

#### Uninterpreted Functions

Uninterpreted functions are documented \ref man_modelling-nondet "here".

### Predefined Types and Symbols

#### \_\_CPROVER\_bitvector

```C
__CPROVER_bitvector [ expression ]
```

This type is only available in the C frontend. It is used to specify a
bit vector with arbitrary but fixed size. The usual integer type
modifiers **signed** and **unsigned** can be applied. The usual
arithmetic promotions will be applied to operands of this type.

#### \_\_CPROVER\_floatbv

```C
__CPROVER_floatbv [ expression ] [ expression ]
```

This type is only available in the C frontend. It is used to specify an
IEEE-754 floating point number with arbitrary but fixed size. The first
parameter is the total size (in bits) of the number, and the second is
the size (in bits) of the mantissa, or significand (not including the
hidden bit, thus for single precision this should be 23).

#### \_\_CPROVER\_fixedbv

```C
__CPROVER_fixedbv [ expression ] [ expression ]
```

This type is only available in the C frontend. It is used to specify a
fixed-point bit vector with arbitrary but fixed size. The first
parameter is the total size (in bits) of the type, and the second is the
number of bits after the radix point.

#### \_\_CPROVER\_size\_t

The type of sizeof expressions.

#### \_\_CPROVER\_rounding\_mode

```C
extern int __CPROVER_rounding_mode;
```

This variable contains the IEEE floating-point arithmetic rounding mode.

#### \_\_CPROVER\_constant\_infinity\_uint

This is a constant that models a large unsigned integer.

#### \_\_CPROVER\_integer, \_\_CPROVER\_rational

**\_\_CPROVER\_integer** is an unbounded, signed integer type.
**\_\_CPROVER\_rational** is an unbounded, signed rational number type.

#### \_\_CPROVER\_memory

```C
extern unsigned char __CPROVER_memory[];
```

This array models the contents of integer-addressed memory.

#### \_\_CPROVER::unsignedbv&lt;N&gt; (C++ only)

This type is the equivalent of **unsigned \_\_CPROVER\_bitvector\[N\]**
in the C++ front-end.

#### \_\_CPROVER::signedbv&lt;N&gt; (C++ only)

This type is the equivalent of **signed \_\_CPROVER\_bitvector\[N\]** in
the C++ front-end.

#### \_\_CPROVER::fixedbv&lt;N&gt; (C++ only)

This type is the equivalent of **\_\_CPROVER\_fixedbv\[N,m\]** in the
C++ front-end.

### Concurrency

Asynchronous threads are created by preceding an instruction with a
label with the prefix **\_\_CPROVER\_ASYNC\_**.

