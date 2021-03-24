# CBMC Assigns Clause

## Introduction

The _assigns_ clause allows the user to specify a list of memory
locations which may be written within a particular scope. While an assigns
clause may, in general, be interpreted with either _writes_ or _modifies_
semantics, this design is based on the former. This means that memory not
captured by the assigns clause must not be written within the given scope, even
if the value(s) therein are not modified.

Assigns clauses currently support simple variable types and their pointers,
structs, and arrays.  Recursive pointer structures are left to future work,
as their support would require changes to CBMC's memory model.


## Syntax
A special construct is introduced to specify assigns clauses. Its syntax is
defined as follows.

```
 <assigns_clause> := __CPROVER_assigns ( <target_list> )
```
```
 <target_list> := __CPROVER_nothing
                | <target>
                | <target_list> , <target>
```
```
 <target> := <deref_target>
           | <target> [ array_index ]
           | <target> [ array_range ]

 <array_index> := <identifier> | <integer>
 <array_range> := <array_index> , <array_index>
```
```
 <deref_target> := <member_target>
                 | * <deref_target>
```
```
 <member_target> := <primary_target>
                  | <member_target> . <member_name>
                  | <member_target> -> <member_name>
```
```
 <primary_target> := <identifier>
                  | ( <target> )
```

The assigns clause identifies a list of targets, which may be an identifier
(e.g. `x`), a member of a struct (e.g. `myStruct.someMember` or
`myStructPtr->otherMember`), a dereferenced pointer (e.g. `*myPtr`), or an
array range (e.g. `myArr[5, lastIdx]`).  The `<assigns_clause>` states that only
memory identified in the target list may be written within the function, as
described in the next section.

For example, consider the following declarations.

```c
struct pair
{
  int x;
  int y;
};

void foo(int *myInt1, int *myInt2, struct pair *myPair, int myArr[], int lastIdx)
__CPROVER_assigns(*myInt1, myPair->y, myArr[5, lastIdx]);
```

This code declares a struct type, called `pair` with 2 members `x` and `y`,
as well as a function `foo` which takes two integer pointer arguments
`myInt1` and `myInt2`, one pair struct pointer `myPair`, and an array
argument `myArr` with an associated last index `lastIdx`.  The assigns
clause attached to this definition states that most of the arguments
can be assigned. However, `myInt2`, `myPair->x`, and the first four
elements of `myArr` should not be assigned in the body of `foo`.

## Semantics
The semantics of an assigns clause *c* of some function *f* can
be understood in two contexts.  First, one may consider how the expressions in
*c* are treated when a call to *f* is replaced by its contract specification,
assuming the contract specification is a sound characterization of the behavior
of *f*.  Second, one may consider how *c* is applied to the function body of *f*
in order to determine whether *c* is a sound characterization of the behavior of
*f*.  To illustrate these two perspectives, consider the following definition of
`foo`.   


```c
void foo(int *myInt1, int *myInt2, struct pair *myPair, int myArr[], int lastIdx)
{
  *myInt1 = 34;
  myPair->y = 55;
  myArr[5] = 89;
}
```

We begin by exploring these two perspectives with a formal definition, and then
an example.

Let the i<sup>th</sup> expression in some assigns clause *c* be denoted
*exprs*<sub>*c*</sub>[i], the j<sup>th</sup> formal parameter of some function
*f* be denoted *params*<sub>*f*</sub>[j], and the k<sup>th</sup> argument passed
in a call to function *f* be denoted *args*<sub>*f*</sub>[k] (an identifying
index may be added to distinguish a *particular* call to *f*, but for simplicity
it is omitted here).

## Replacement
Assuming an assigns clause *c* is a sound characterization of
the behavior of the function *f*, a call to *f* may be replaced a series of
non-deterministic assignments. For each expression *e* &#8712;
*exprs*<sub>*c*</sub>, let there be an assignment &#632; := &#8727;, where
&#632; is *args*<sub>*f*</sub>[i] if *e* is identical to some
*params*<sub>*f*</sub>[i], and *e* otherwise.  For array ranges, create an
assignment for each element in the array range.

In the case where *f* is `foo`, and some function `bar` calls `foo`

```c
void bar()
{
  int a, b;
  int arr[8];
  struct pair p;

  foo(&a, &b, &p, arr, 7);
}
```

the call to `foo` is replaced by the following series of assignments.

```c
void bar()
{
  int a, b;
  int arr[10];
  struct pair p;

  a = *;
  p.y = *;
  arr[5] = *;
  arr[6] = *;
  arr[7] = *;
}
```

## Enforcement
In order to determine whether an assigns clause *c* is a
sound characterization of the behavior of a function *f*, the body of the
function is instrumented with assertion statements before each statement which
may write to memory (e.g. an assignment).  These assertions are based on the
assignable targets *exprs*<sub>*c*</sub> identified in the assigns clause.

While sequentially traversing the function body, CBMC instruments statements
that might modify memory a preceding assertion to ensure that they only
modify assignable memory.  These assertions consist of a disjunction
where each disjunct depends on the type of the assignable target.

- For an assignable target expression *e* of scalar type:

```c
__CPROVER_POINTER_OBJECT(&lhs) == __CPROVER_POINTER_OBJECT(&e) &&
__CPROVER_POINTER_OFFSET(&lhs) == __CPROVER_POINTER_OFFSET(&e)
```

- For an assignable target expression *e* of struct type, a similar disjunct is
  created, with an additional size comparison:

```c
__CPROVER_POINTER_OBJECT(&lhs) == __CPROVER_POINTER_OBJECT(&e) &&
__CPROVER_POINTER_OFFSET(&lhs) == __CPROVER_POINTER_OFFSET(&e) &&
sizeof(lhs) == sizeof(e)
```

Additionally, for each member m of *e*, we add an extra disjunct:

```c
__CPROVER_POINTER_OBJECT(&lhs) == __CPROVER_POINTER_OBJECT(&(e->m)) &&
__CPROVER_POINTER_OFFSET(&lhs) == __CPROVER_POINTER_OFFSET(&(e->m)) &&
sizeof(lhs) == sizeof(e->m)
```

This extension is performed recursively in the
case that some member of a struct is also a struct.

- For an assignable target expression *e* of array range type, `a[lo, hi]`, a
  disjunct is created using the array pointer `a` and the range bounds `lo` and
`hi`:

```c
__CPROVER_POINTER_OBJECT(&lhs) == __CPROVER_POINTER_OBJECT(a) &&
__CPROVER_POINTER_OFFSET(&lhs) >= lo * sizeof(a[0]) &&
__CPROVER_POINTER_OFFSET(&lhs) <= hi * sizeof(a[0])
```

This effectively creates an assertion that the memory location being assigned
falls within the assignable memory identified by the assigns clause.  In
practice, temporary variables are used to ensure that the assignable memory
doesn't change during function execution, but here we have used the assignable
targets directly for readability.  Function calls are handled similarly, based
on the memory their assigns clause indicates that they can modify.
Additionally, for each function call without an assigns clause, we add an
assertion assert(*false*) to ensure that the assigns contract will only hold if
all called functions have an assigns clause which is compatible with that of the
calling function.

For the earlier example, `foo` would be instrumented as follows:


```c
void foo(int *myInt1, int *myInt2, struct pair *myPair, int myArr[], int lastIdx)
{
  int *temp1 = myInt1;
  int *temp2 = &(myPair->y);
  int *temp3 = myArr;
  int temp4 = 5 * sizeof(iint);
  int temp5 = lastIdx * sizeof(int);

  assert((__CPROVER_POINTER_OBJECT(myInt1) == __CPROVER_POINTER_OBJECT(temp1) &&
          __CPROVER_POINTER_OFFSET(myInt1) == __CPROVER_POINTER_OFFSET(temp1)) ||
         (__CPROVER_POINTER_OBJECT(myInt1) == __CPROVER_POINTER_OBJECT(temp2) &&
          __CPROVER_POINTER_OFFSET(myInt1) == __CPROVER_POINTER_OFFSET(temp2)) ||
         (__CPROVER_POINTER_OBJECT(myInt1) == __CPROVER_POINTER_OBJECT(temp3) &&
          __CPROVER_POINTER_OFFSET(myInt1) >= temp4 &&
          __CPROVER_POINTER_OFFSET(myInt1) <= temp5)
        );
  *myInt1 = 34;

  assert((__CPROVER_POINTER_OBJECT(&(myPair->y)) == __CPROVER_POINTER_OBJECT(temp1) &&
          __CPROVER_POINTER_OFFSET(&(myPair->y)) == __CPROVER_POINTER_OFFSET(temp1)) ||
         (__CPROVER_POINTER_OBJECT(&(myPair->y)) == __CPROVER_POINTER_OBJECT(temp2) &&
          __CPROVER_POINTER_OFFSET(&(myPair->y)) == __CPROVER_POINTER_OFFSET(temp2)) ||
         (__CPROVER_POINTER_OBJECT(&(myPair->y)) == __CPROVER_POINTER_OBJECT(temp3) &&
          __CPROVER_POINTER_OFFSET(&(myPair->y)) >= temp4 &&
          __CPROVER_POINTER_OFFSET(&(myPair->y)) <= temp5)
        );
  myPair->y = 55;

  assert((__CPROVER_POINTER_OBJECT(&(myArr[5])) == __CPROVER_POINTER_OBJECT(temp1) &&
          __CPROVER_POINTER_OFFSET(&(myArr[5])) == __CPROVER_POINTER_OFFSET(temp1)) ||
         (__CPROVER_POINTER_OBJECT(&(myArr[5])) == __CPROVER_POINTER_OBJECT(temp2) &&
          __CPROVER_POINTER_OFFSET(&(myArr[5])) == __CPROVER_POINTER_OFFSET(temp2)) ||
         (__CPROVER_POINTER_OBJECT(&(myArr[5])) == __CPROVER_POINTER_OBJECT(temp3) &&
          __CPROVER_POINTER_OFFSET(&(myArr[5])) >= temp4 &&
          __CPROVER_POINTER_OFFSET(&(myArr[5])) <= temp5)
        );
  myArr[5] = 89;
}
```

Additionally, the set of assignable target expressions is updated while
traversing the function body when new memory is allocated.  For example, the
statement `x = (int *)malloc(sizeof(int))` would create a pointer, stored in
`x`, to assignable memory. Since the memory is allocated within the current
function, there is no way an assignment to this memory can affect the memory of
the calling context.  If memory is allocated for a struct, the subcomponents are
considered assignable as well.

Finally, a set of freely-assignable symbols *free* is tracked during the
traversal of the function body. These are locally-defined variables and formal
parameters without dereferences.  For example, in a variable declaration `<type>
x = <initial_value>`, `x` would be added to *free*. Assignment statements (i.e.,
where the left-hand-side is in *free*) are not instrumented with
the above assertions.
