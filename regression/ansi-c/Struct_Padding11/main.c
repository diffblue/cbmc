// GCC packed structs: every member is byte-aligned -- including a member
// whose TYPE is aligned -- except for a member carrying its own `aligned(n)'
// attribute, which keeps exactly n; the struct's alignment is the maximum of
// those (and of its own `aligned', if any), with tail padding to match.  An
// unnamed bit-field (zero-width or not) aligns what follows but never raises
// the struct's alignment (System V ABI).  Values: gcc 13 / clang 18, x86-64.
#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__
#include <stddef.h>

struct A
{
  int x;
} __attribute__((aligned(16)));
struct P1
{
  char c;
  struct A a;
} __attribute__((packed));
struct P2
{
  char c;
  int x __attribute__((aligned(4)));
} __attribute__((packed));
struct P3
{
  char c;
  int x __attribute__((aligned(2)));
  char d;
} __attribute__((packed));
struct P4
{
  char c;
  short s;
  void *p __attribute__((packed, aligned(4)));
} __attribute__((packed));
struct P5
{
  char c;
  struct A a __attribute__((aligned(8)));
} __attribute__((packed));
struct P6
{
  char c;
  long l[1] __attribute__((packed, aligned(2)));
} __attribute__((packed));
struct P7
{
  char c;
  struct A a;
};
struct B1
{
  char c;
  long long l __attribute__((aligned(8)));
} __attribute__((packed, aligned(4)));

STATIC_ASSERT(sizeof(struct P1) == 17 && _Alignof(struct P1) == 1);
STATIC_ASSERT(offsetof(struct P1, a) == 1);
STATIC_ASSERT(sizeof(struct P2) == 8 && _Alignof(struct P2) == 4);
STATIC_ASSERT(offsetof(struct P2, x) == 4);
STATIC_ASSERT(sizeof(struct P3) == 8 && _Alignof(struct P3) == 2);
STATIC_ASSERT(offsetof(struct P3, x) == 2);
STATIC_ASSERT(sizeof(struct P4) == 12 && _Alignof(struct P4) == 4);
STATIC_ASSERT(offsetof(struct P4, p) == 4);
STATIC_ASSERT(sizeof(struct P5) == 24 && _Alignof(struct P5) == 8);
STATIC_ASSERT(offsetof(struct P5, a) == 8);
STATIC_ASSERT(sizeof(struct P6) == 10 && _Alignof(struct P6) == 2);
STATIC_ASSERT(offsetof(struct P6, l) == 2);
STATIC_ASSERT(sizeof(struct P7) == 32 && _Alignof(struct P7) == 16);
STATIC_ASSERT(offsetof(struct P7, a) == 16);
STATIC_ASSERT(sizeof(struct B1) == 16 && _Alignof(struct B1) == 8);
STATIC_ASSERT(offsetof(struct B1, l) == 8);

// zero-width bit-fields in packed structs
struct Z1
{
  char c;
  unsigned : 0;
  char d;
} __attribute__((packed));
struct Z2
{
  char c;
  int b : 3;
  unsigned : 0;
  char d;
} __attribute__((packed));
struct Z3
{
  char c;
  int b : 3;
  short s : 2;
} __attribute__((packed));
struct Z4
{
  char c;
  int b : 20;
} __attribute__((packed));
STATIC_ASSERT(sizeof(struct Z1) == 5 && _Alignof(struct Z1) == 1);
STATIC_ASSERT(offsetof(struct Z1, d) == 4);
STATIC_ASSERT(sizeof(struct Z2) == 5 && _Alignof(struct Z2) == 1);
STATIC_ASSERT(offsetof(struct Z2, d) == 4);
STATIC_ASSERT(sizeof(struct Z3) == 2 && _Alignof(struct Z3) == 1);
STATIC_ASSERT(sizeof(struct Z4) == 4 && _Alignof(struct Z4) == 1);

// unnamed bit-fields do not affect the alignment
struct A1
{
  char c;
  int : 0;
  char d;
};
struct A2
{
  char c;
  int : 3;
  char d;
};
struct A3
{
  char c;
  unsigned short : 9;
  char d;
};
struct A4
{
  unsigned short : 0;
};
struct A5
{
  char c;
  int x : 3;
  char d;
};
STATIC_ASSERT(sizeof(struct A1) == 5 && _Alignof(struct A1) == 1);
STATIC_ASSERT(offsetof(struct A1, d) == 4);
STATIC_ASSERT(sizeof(struct A2) == 3 && _Alignof(struct A2) == 1);
STATIC_ASSERT(offsetof(struct A2, d) == 2);
STATIC_ASSERT(sizeof(struct A3) == 5 && _Alignof(struct A3) == 1);
STATIC_ASSERT(offsetof(struct A3, d) == 4);
STATIC_ASSERT(sizeof(struct A4) == 0 && _Alignof(struct A4) == 1);
STATIC_ASSERT(sizeof(struct A5) == 4 && _Alignof(struct A5) == 4);
STATIC_ASSERT(offsetof(struct A5, d) == 2);
#endif

int main()
{
  return 0;
}
