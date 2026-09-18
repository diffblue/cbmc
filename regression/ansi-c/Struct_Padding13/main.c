// GCC: an `aligned(k)' attribute on a declaration only increases the
// alignment; the alignment of an aligned typedef stays when it is the larger.
// Together with `packed' the attribute sets the alignment exactly.
// Values: gcc 13 / clang 18.
#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__
typedef int __attribute__((aligned(1))) T1;
typedef int __attribute__((aligned(16))) T16;
struct A
{
  char c;
  T1 x __attribute__((aligned(4))); // 4 > 1: raised to 4
};
struct B
{
  char c;
  T16 x __attribute__((aligned(4))); // 4 < 16: the typedef's 16 stays
};
struct C
{
  char c;
  T1 x; // the typedef lowers the alignment to 1
};
struct D
{
  char c;
  T16 x __attribute__((packed, aligned(4))); // packed + aligned: exactly 4
};
union U
{
  T16 m __attribute__((packed, aligned(1)));
  int i;
};
typedef unsigned char __attribute__((aligned(8))) T8c;
struct W
{
  char c;
  T8c x __attribute__((aligned(4))); // packed struct: the member's own 4 counts, the typedef's 8 not
} __attribute__((packed));
#pragma pack(push, 1)
struct X
{
  int m3 : 2;
  unsigned short m4[5] __attribute__((aligned(8))); // pack(1) caps the member's aligned(8): at 1
  signed char m5 : 6;
  long long m6;
} __attribute__((packed, aligned(16)));
#pragma pack(pop)
#pragma pack(push, 4)
struct V
{
  char c;
  union { long a; } __attribute__((aligned(16))) u; // placed at 4, 16 bytes long
  char d;
};
#pragma pack(pop)

STATIC_ASSERT(_Alignof(struct A) == 4);
STATIC_ASSERT(__builtin_offsetof(struct A, x) == 4);
STATIC_ASSERT(_Alignof(struct B) == 16);
STATIC_ASSERT(__builtin_offsetof(struct B, x) == 16);
STATIC_ASSERT(_Alignof(struct C) == 1);
STATIC_ASSERT(__builtin_offsetof(struct C, x) == 1);
STATIC_ASSERT(_Alignof(struct D) == 4);
STATIC_ASSERT(__builtin_offsetof(struct D, x) == 4);
STATIC_ASSERT(_Alignof(union U) == 4);
STATIC_ASSERT(sizeof(union U) == 4);
STATIC_ASSERT(__builtin_offsetof(struct W, x) == 4);
STATIC_ASSERT(sizeof(struct W) == 8);
STATIC_ASSERT(__builtin_offsetof(struct X, m4) == 1);
STATIC_ASSERT(__builtin_offsetof(struct X, m6) == 12);
STATIC_ASSERT(sizeof(struct X) == 32);
STATIC_ASSERT(_Alignof(struct X) == 16);
STATIC_ASSERT(__builtin_offsetof(struct V, u) == 4);
STATIC_ASSERT(__builtin_offsetof(struct V, d) == 20);
STATIC_ASSERT(sizeof(struct V) == 24);
#endif

int main()
{
}
