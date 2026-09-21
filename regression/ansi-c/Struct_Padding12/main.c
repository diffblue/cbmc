// GCC `#pragma pack(n)': a member is placed at min(n, max(natural, its own
// aligned(k))); `packed' on the struct still byte-aligns; struct-typed members
// are capped too; bit-fields are laid out densely under the pragma while a
// zero-width bit-field aligns to its type's full alignment; a named bit-field
// of a packed struct under the pragma contributes min(n, natural).  Alignment
// specifiers in the declaration specifiers apply to the declared pointer; an
// `aligned' on an in-place anonymous member type is ignored in a packed struct;
// an attribute on an array member is the member's.  Values: gcc 13/clang 18.
#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__
#  include <stdbool.h>
#  include <stddef.h>

#  pragma pack(push, 4)
struct A
{
  float m;
} __attribute__((packed));
struct B
{
  char c;
  double d;
};
struct C
{
  char c;
  short s;
  long l;
} __attribute__((packed));
#  pragma pack(pop)
STATIC_ASSERT(sizeof(struct A) == 4 && _Alignof(struct A) == 1);
STATIC_ASSERT(sizeof(struct B) == 12 && _Alignof(struct B) == 4);
STATIC_ASSERT(offsetof(struct B, d) == 4);
STATIC_ASSERT(sizeof(struct C) == 11 && _Alignof(struct C) == 1);

#  pragma pack(push, 1)
struct D
{
  long m __attribute__((aligned(4)));
  char c;
};
struct E
{
  char c;
  union
  {
    double d;
  };
  bool b : 1;
};
struct F
{
  char c;
  int i __attribute__((aligned(8)));
};
#  pragma pack(pop)
STATIC_ASSERT(sizeof(struct D) == 9 && _Alignof(struct D) == 1);
STATIC_ASSERT(sizeof(struct E) == 10 && _Alignof(struct E) == 1);
STATIC_ASSERT(offsetof(struct E, d) == 1);
STATIC_ASSERT(sizeof(struct F) == 5 && offsetof(struct F, i) == 1);

#  pragma pack(push, 8)
struct G
{
  char c;
  int i __attribute__((aligned(2)));
};
struct H
{
  char c;
  int i __attribute__((aligned(16)));
};
struct I
{
  char c;
  short s : 14;
  char d;
};
struct J
{
  char c;
  int i : 31;
  char d;
};
#  pragma pack(pop)
STATIC_ASSERT(sizeof(struct G) == 8 && offsetof(struct G, i) == 4);
STATIC_ASSERT(sizeof(struct H) == 16 && offsetof(struct H, i) == 8);
STATIC_ASSERT(sizeof(struct I) == 4 && offsetof(struct I, d) == 3);
STATIC_ASSERT(sizeof(struct J) == 8 && offsetof(struct J, d) == 5);

#  pragma pack(push, 2)
struct K
{
  char c;
  int i __attribute__((aligned(8)));
  double d;
};
struct L
{
  char c;
  struct B b;
};
struct M
{
  char c;
  long long : 0;
  char d;
};
struct N
{
  short m : 9;
  bool b[8];
} __attribute__((packed));
union O
{
  int i[8];
  void *p;
};
#  pragma pack(pop)
STATIC_ASSERT(sizeof(struct K) == 14 && offsetof(struct K, i) == 2);
STATIC_ASSERT(offsetof(struct K, d) == 6);
STATIC_ASSERT(sizeof(struct L) == 14 && offsetof(struct L, b) == 2);
STATIC_ASSERT(sizeof(struct M) == 9 && offsetof(struct M, d) == 8);
STATIC_ASSERT(sizeof(struct N) == 10 && _Alignof(struct N) == 2);
STATIC_ASSERT(sizeof(union O) == 32 && _Alignof(union O) == 2);

// alignment specifiers on pointer members, in-place anonymous types, arrays
union P
{
  void *p[5];
  _Alignas(16) void *q;
} __attribute__((packed));
struct Q
{
  char c;
  _Alignas(16) void *q;
} __attribute__((packed));
struct R
{
  struct
  {
    long long a;
  } __attribute__((packed, aligned(8)));
} __attribute__((packed));
struct S
{
  _Alignas(32) char m[3];
  char c;
} __attribute__((packed));
STATIC_ASSERT(sizeof(union P) == 48 && _Alignof(union P) == 16);
STATIC_ASSERT(sizeof(struct Q) == 32 && _Alignof(struct Q) == 16);
STATIC_ASSERT(offsetof(struct Q, q) == 16);
STATIC_ASSERT(sizeof(struct R) == 8 && _Alignof(struct R) == 1);
STATIC_ASSERT(sizeof(struct S) == 32 && _Alignof(struct S) == 32);
#endif

int main()
{
  return 0;
}
