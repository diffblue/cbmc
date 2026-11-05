#include <stddef.h>

// An alignment attribute in a declaration applies to the declared entity,
// irrespective of its position: for members and objects it can only increase
// the alignment (also in packed aggregates), whereas for typedefs it sets the
// alignment of the type, which packing then overrides.

// attributes in the declaration specifiers apply to array and pointer members
// as a whole
struct D1
{
  char c;
  __attribute__((aligned(16))) char *m;
};
struct D2
{
  char c;
  long __attribute__((aligned(2))) m[2];
} __attribute__((packed));
struct D3
{
  char c;
  __attribute__((aligned(2))) void *m;
} __attribute__((packed));
struct X
{
  long l;
};
struct D4
{
  char c;
  __attribute__((aligned(16))) struct X m;
} __attribute__((packed));
struct D5
{
  char c;
  struct X m __attribute__((aligned(16)));
} __attribute__((packed));

_Static_assert(offsetof(struct D1, m) == 16, "D1");
_Static_assert(offsetof(struct D2, m) == 2 && _Alignof(struct D2) == 2, "D2");
_Static_assert(offsetof(struct D3, m) == 2 && _Alignof(struct D3) == 2, "D3");
_Static_assert(offsetof(struct D4, m) == 16, "D4");
_Static_assert(offsetof(struct D5, m) == 16, "D5");

// the alignment of a typedef'd type is overridden by packing
typedef int T2 __attribute__((aligned(2)));
typedef struct X TX16 __attribute__((aligned(16)));
struct P1
{
  char c;
  T2 m;
} __attribute__((packed));
struct P2
{
  char c;
  TX16 m;
} __attribute__((packed));
struct P3
{
  char c;
  T2 m __attribute__((packed));
};

_Static_assert(offsetof(struct P1, m) == 1 && _Alignof(struct P1) == 1, "P1");
_Static_assert(offsetof(struct P2, m) == 1 && _Alignof(struct P2) == 1, "P2");
_Static_assert(offsetof(struct P3, m) == 1 && _Alignof(struct P3) == 1, "P3");

// so are the attributes of a struct definition
struct I
{
  long l;
} __attribute__((packed, aligned(4)));
struct P4
{
  char c;
  struct I m;
};
struct P5
{
  char c;
  struct I m;
} __attribute__((packed));
struct P6
{
  char c;
  struct X2
  {
    long l;
  } __attribute__((aligned(16))) m;
} __attribute__((packed));

_Static_assert(offsetof(struct P4, m) == 4, "P4");
_Static_assert(offsetof(struct P5, m) == 1, "P5");
_Static_assert(offsetof(struct P6, m) == 1 && sizeof(struct P6) == 17, "P6");

// a typedef may reduce the alignment, and a member's own alignment attribute
// can only increase the resulting alignment
typedef void *TP1 __attribute__((aligned(1)));
typedef struct X TX1 __attribute__((aligned(1)));
struct R1
{
  char c;
  TP1 m __attribute__((aligned(1)));
};
struct R2
{
  char c;
  TP1 m __attribute__((aligned(4)));
};
struct R3
{
  char c;
  TX1 m;
};

_Static_assert(offsetof(struct R1, m) == 1 && _Alignof(struct R1) == 1, "R1");
_Static_assert(offsetof(struct R2, m) == 4 && _Alignof(struct R2) == 4, "R2");
_Static_assert(offsetof(struct R3, m) == 1 && _Alignof(TX1) == 1, "R3");

// an alignment attribute on a struct definition can only increase alignment
struct Y
{
  long l;
} __attribute__((aligned(1)));
struct R4
{
  char c;
  struct Y m;
};

_Static_assert(offsetof(struct R4, m) == 8 && _Alignof(struct Y) == 8, "R4");

// all alignment attributes of a typedef apply to the type being defined
typedef __attribute__((aligned(16))) char *Q1;
typedef char __attribute__((aligned(16))) * Q2;
typedef char *Q3 __attribute__((aligned(16)));
typedef char *__attribute__((aligned(2))) Q4;
typedef __attribute__((aligned(2))) char *Q5;
typedef char A1[2] __attribute__((aligned(16)));
typedef __attribute__((aligned(16))) char A2[2];

_Static_assert(_Alignof(Q1) == 16, "Q1");
_Static_assert(_Alignof(Q2) == 16, "Q2");
_Static_assert(_Alignof(Q3) == 16, "Q3");
_Static_assert(_Alignof(Q4) == 2, "Q4");
_Static_assert(_Alignof(Q5) == 2, "Q5");
_Static_assert(_Alignof(A1) == 16, "A1");
_Static_assert(_Alignof(A2) == 16, "A2");

// for objects, an alignment attribute may also reduce the alignment
__attribute__((aligned(16))) char *o1;
char *o2 __attribute__((aligned(16)));
long o3 __attribute__((aligned(1)));
struct
{
  char c;
  long m __attribute__((aligned(16)));
} o4;

_Static_assert(__alignof__(o1) == 16, "o1");
_Static_assert(__alignof__(o2) == 16, "o2");
_Static_assert(__alignof__(o3) == 1, "o3");
_Static_assert(__alignof__(o4.m) == 16, "o4");

// the alignment of a declaration is not part of the type that __typeof__
// yields
struct T1
{
  int m __attribute__((aligned(32)));
} t1;
__typeof__(t1.m) *t1p;
struct T2
{
  char c;
  __typeof__(t1.m) *q;
};
struct T3
{
  char c;
  __typeof__(o3) m;
};

_Static_assert(_Alignof(__typeof__(t1p)) == 8, "t1p");
_Static_assert(offsetof(struct T2, q) == 8, "T2");
_Static_assert(offsetof(struct T3, m) == 8, "T3");

// a plain aligned attribute does not discard an explicit alignment
struct B1
{
  char c;
  __attribute__((aligned(32))) char x[2] __attribute__((aligned));
};

_Static_assert(offsetof(struct B1, x) == 32, "B1");

// an alignment attribute on a bit-field also aligns its start
struct BF1
{
  char c;
  int b : 3 __attribute__((aligned(8)));
};
struct BF2
{
  char c;
  __attribute__((aligned(8))) int b : 3;
  char d;
};
struct BF3
{
  char c;
  int b : 3 __attribute__((aligned(8)));
} __attribute__((packed));
#pragma pack(push, 2)
struct BF4
{
  char c;
  int b : 3 __attribute__((aligned(8)));
  char d;
};
#pragma pack(pop)
struct BF5
{
  char c : 3;
  int b : 3 __attribute__((aligned(4)));
  char d;
};

_Static_assert(sizeof(struct BF1) == 16 && _Alignof(struct BF1) == 8, "BF1");
_Static_assert(sizeof(struct BF2) == 16 && offsetof(struct BF2, d) == 9, "BF2");
_Static_assert(sizeof(struct BF3) == 16 && _Alignof(struct BF3) == 8, "BF3");
_Static_assert(sizeof(struct BF4) == 4 && _Alignof(struct BF4) == 2, "BF4");
_Static_assert(sizeof(struct BF5) == 8 && offsetof(struct BF5, d) == 5, "BF5");

// anonymous aggregates differing only in member alignment are distinct
struct
{
  int x __attribute__((aligned(8)));
  int y;
} an1;
struct
{
  int x;
  int y;
} an2;

_Static_assert(__alignof__(an1) == 8 && __alignof__(an2) == 4, "anon");

// GCC applies an alignment attribute following the '*' of a pointer
// declarator to the pointer type (which then behaves like a typedef'd type),
// whereas Clang applies it to the declared entity
struct G1
{
  char c;
  void *__attribute__((aligned(2))) m;
};
struct G2
{
  char c;
  void *__attribute__((aligned(2))) m;
} __attribute__((packed));
struct G3
{
  char c;
  void *__attribute__((aligned(1))) m[2];
};
// but not to an attribute following the declarator
struct G4
{
  char c;
  void *m __attribute__((aligned(2)));
};

#ifdef __clang__
_Static_assert(offsetof(struct G1, m) == 8, "G1");
_Static_assert(offsetof(struct G2, m) == 2, "G2");
_Static_assert(offsetof(struct G3, m) == 8, "G3");
#else
_Static_assert(offsetof(struct G1, m) == 2, "G1");
_Static_assert(offsetof(struct G2, m) == 1, "G2");
_Static_assert(offsetof(struct G3, m) == 1, "G3");
#endif
_Static_assert(offsetof(struct G4, m) == 8, "G4");

int main()
{
  return 0;
}
