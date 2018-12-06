[CPROVER Manual TOC](../../)

## Pointer Model

### Pointers in C

C programs (and sometimes C++ programs as well) make intensive use of
pointers in order to decouple program code from specific data. A pointer
variable does not store data such as numbers or letters, but instead
points to a location in memory that hold the relevant data. This section
describes the way the CPROVER tools model pointers.

### Objects and Offsets

The CPROVER tools represent pointers as a pair. The first member of the
pair is the *object* the pointer points to, and the second is the offset
within the object.

In C, objects are simply continuous fragments of memory (this definition
of "object" is not to be confused with the use of the term in
object-oriented programming). Variables of any type are guaranteed to be
stored as one object, irrespective of their type. As an example, all
members of a struct or array belong to the same object. CPROVER simply
assigns a number to each active object. The object number of a pointer
`p` can be extracted using the expression `__CPROVER_POINTER_OBJECT(p)`.
As a consequence, pointers to different objects are always different,
which is not sound.

The offset (the second member of the pair that forms a pointer) is
relative to the beginning of the object; it uses byte granularity. As an
example, the code fragment:

```C
unsigned array[10];
char *p;

p=(char *)(array+1);
p++;
```

will result in a pointer with offset 5. The offset of a pointer `p` can
be extracted using the expression `__CPROVER_POINTER_OFFSET(p)`.

### Dereferencing Pointers

The CPROVER tools require that pointers that are dereferenced point to a
valid object. Assertions that check this requirement can be generated
using the option --pointer-check and, if desired, --bounds-check. These
options will ensure that NULL pointers are not dereferenced, and that
dynamically allocated objects have not yet been deallocated.

Furthermore, the CPROVER tools check that dynamically allocated memory
is not deallocated twice. The goto-instrument tool is also able to add
checks for memory leaks, that is, it detects dynamically allocated objects
that are not deallocated once the program terminates.

The CPROVER tools support pointer typecasts. Most casts are supported,
with the following exceptions:

1.  Pointers can only be accessed using a
    pointer type. The conversion of a pointer into an integer type using
    a pointer typecast is not supported.

2.  Casts from integers to pointers yield a pointer that is either NULL
    (if the integer is zero) or that point into a special array for
    modeling [memory-mapped
    I/O](http://en.wikipedia.org/wiki/Memory-mapped_I/O). Such pointers
    are assumed not to overlap with any other objects. This is, of
    course, only sound if a corresponding range check is instrumented.

3.  Accesses to arrays via pointers that have the array subtype need to
    be well-aligned.

### Pointers in Open Programs

It is frequently desired to validate an open program (a fragment
of a program). Some variables are left undefined. When an undefined
pointer is dereferenced, CBMC assumes that the pointer points to a
separate object of appropriate type with unbounded size. The object is
assumed not to alias with any other object. This assumption may
obviously be wrong in specific extensions of the program.

