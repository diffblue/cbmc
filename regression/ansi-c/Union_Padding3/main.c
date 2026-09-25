// GCC unions: `packed, aligned(n)' gives exactly n; a packed union with an
// aligned(n) member has alignment n and is padded to it; `aligned(n)' alone
// pads the size to n.  Values: gcc 13 / clang 18, x86-64.
#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__
#  include <stddef.h>

union U1
{
  unsigned short a : 9;
  unsigned short b : 13;
} __attribute__((packed, aligned(16)));
union U2
{
  unsigned short a : 9;
  char c;
} __attribute__((packed));
union U3
{
  int a;
  char c[5];
} __attribute__((aligned(8)));
union U4
{
  _Bool m[8] __attribute__((aligned(16)));
} __attribute__((packed));
union U5
{
  char c;
  double d[5] __attribute__((aligned(16)));
  int b : 12;
} __attribute__((packed));
STATIC_ASSERT(sizeof(union U1) == 16 && _Alignof(union U1) == 16);
STATIC_ASSERT(sizeof(union U2) == 2 && _Alignof(union U2) == 1);
STATIC_ASSERT(sizeof(union U3) == 8 && _Alignof(union U3) == 8);
STATIC_ASSERT(sizeof(union U4) == 16 && _Alignof(union U4) == 16);
STATIC_ASSERT(sizeof(union U5) == 48 && _Alignof(union U5) == 16);
#endif

int main()
{
  return 0;
}
