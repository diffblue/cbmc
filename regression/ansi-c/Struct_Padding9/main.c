// GCC: `aligned(n)' together with `packed' sets the alignment to exactly n
// ("the aligned attribute can only increase the alignment; but you can
// decrease it by specifying packed as well").  `struct H' therefore has
// alignment 16 (not min(16, 2) = 2), and a member of that type is placed on
// a 16-byte boundary.  #pragma pack(n), by contrast, only caps the member
// alignment at n.
#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__
#  include <stddef.h>

struct H
{
  unsigned short a;
  unsigned short b;
} __attribute__((packed, aligned(16)));
STATIC_ASSERT(sizeof(struct H) == 16);
STATIC_ASSERT(_Alignof(struct H) == 16);

struct Q
{
  char c;
  struct H h;
};
STATIC_ASSERT(sizeof(struct Q) == 32);
STATIC_ASSERT(_Alignof(struct Q) == 16);
STATIC_ASSERT(offsetof(struct Q, h) == 16);

// member: packed + aligned(2) gives exactly 2
struct M
{
  char c;
  int x __attribute__((packed, aligned(2)));
};
STATIC_ASSERT(sizeof(struct M) == 6);
STATIC_ASSERT(_Alignof(struct M) == 2);
STATIC_ASSERT(offsetof(struct M, x) == 2);

// aligned(8) on the struct, packed member
struct P
{
  char c;
  int x __attribute__((packed));
} __attribute__((aligned(8)));
STATIC_ASSERT(sizeof(struct P) == 8);
STATIC_ASSERT(_Alignof(struct P) == 8);
STATIC_ASSERT(offsetof(struct P, x) == 1);

// #pragma pack(n) caps at n: a short keeps its natural alignment 2
#  pragma pack(push, 4)
struct R
{
  char c;
  short s;
  long long l;
};
#  pragma pack(pop)
STATIC_ASSERT(sizeof(struct R) == 12);
STATIC_ASSERT(offsetof(struct R, s) == 2);
STATIC_ASSERT(offsetof(struct R, l) == 4);
#endif

int main()
{
  return 0;
}
