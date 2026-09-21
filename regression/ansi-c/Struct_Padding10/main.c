// GCC: the `aligned' attribute on a struct, a member or a variable can only
// INCREASE the alignment ("you can decrease it by specifying packed as
// well"); as part of a typedef it sets the alignment exactly, in either
// direction (`typedef uint32_t __attribute__((aligned(1))) unaligned_u32;').
// The values below are those of gcc 13 and clang 18 on x86-64.
#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__
#  include <stddef.h>
#  include <stdint.h>

typedef uint32_t __attribute__((aligned(1))) unaligned_u32;
struct S
{
  int a;
  int b;
};
typedef struct S __attribute__((aligned(2))) S2;
typedef struct S __attribute__((aligned(16))) S16;
struct M
{
  char c;
  int x __attribute__((aligned(2)));
};
struct N
{
  char c;
  unaligned_u32 u;
};
struct P
{
  char c;
  S2 s;
};
struct Q
{
  char c;
  S16 s;
};
struct R
{
  int a;
} __attribute__((aligned(2)));
struct T
{
  int m4;
  unsigned long m5[2] __attribute__((aligned(4)));
  char m6;
};

STATIC_ASSERT(_Alignof(unaligned_u32) == 1);
STATIC_ASSERT(sizeof(S2) == 8 && _Alignof(S2) == 2);
STATIC_ASSERT(sizeof(S16) == 8 && _Alignof(S16) == 16);
STATIC_ASSERT(sizeof(struct M) == 8 && offsetof(struct M, x) == 4);
STATIC_ASSERT(sizeof(struct N) == 5 && offsetof(struct N, u) == 1);
STATIC_ASSERT(sizeof(struct P) == 10 && offsetof(struct P, s) == 2);
STATIC_ASSERT(sizeof(struct Q) == 32 && offsetof(struct Q, s) == 16);
STATIC_ASSERT(sizeof(struct R) == 4 && _Alignof(struct R) == 4);
STATIC_ASSERT(sizeof(struct T) == 32 && offsetof(struct T, m5) == 8);
#endif

int main()
{
  return 0;
}
