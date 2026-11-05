#include <stddef.h>

// #pragma pack(n) caps the alignment of each member at n. This cap is
// independent of, and interacts with, packed and aligned attributes.

#pragma pack(push, 2)
// packing still reduces the alignment of members to 1
union U1
{
  long long m0;
} __attribute__((packed));
// an aligned attribute on the aggregate is not capped by the pragma
struct S2
{
  void *m0;
} __attribute__((aligned(4)));
// an aligned attribute on a member is capped by the pragma
struct S3
{
  char c;
  long long m0 __attribute__((aligned(8)));
};
// members of aggregate type are capped as well
struct S4
{
  char c;
  struct
  {
    int x;
  } m0;
};
#pragma pack(pop)

#pragma pack(push, 1)
struct S5
{
  short m0 __attribute__((aligned(2)));
};
#pragma pack(pop)

_Static_assert(sizeof(union U1) == 8, "");
_Static_assert(_Alignof(union U1) == 1, "");
_Static_assert(sizeof(struct S2) == 8, "");
_Static_assert(_Alignof(struct S2) == 4, "");
_Static_assert(offsetof(struct S3, m0) == 2, "");
_Static_assert(sizeof(struct S3) == 10, "");
_Static_assert(_Alignof(struct S3) == 2, "");
_Static_assert(offsetof(struct S4, m0) == 2, "");
_Static_assert(sizeof(struct S4) == 6, "");
_Static_assert(_Alignof(struct S4) == 2, "");
_Static_assert(sizeof(struct S5) == 2, "");
_Static_assert(_Alignof(struct S5) == 1, "");

// anonymous aggregates that only differ in their packing are distinct types
struct
{
  int i;
} a1;
#pragma pack(push, 1)
struct
{
  int i;
} a2;
#pragma pack(pop)
struct
{
  int i;
} __attribute__((packed)) a3;

_Static_assert(__alignof__(a1) == 4, "");
_Static_assert(__alignof__(a2) == 1, "");
_Static_assert(__alignof__(a3) == 1, "");

// Compilers differ in which #pragma pack applies when it changes within the
// definition of an aggregate: GCC uses the value in effect at the closing
// brace, Clang uses the value in effect at the start of the definition (and
// Visual Studio uses the value in effect at each member, see pragma_pack7).
#pragma pack(push, 1)
struct C1
{
  char c;
#pragma pack(pop)
  int i;
};
struct C2
{
  char c;
#pragma pack(push, 1)
  int i;
};
#pragma pack(pop)

#ifdef __clang__
_Static_assert(sizeof(struct C1) == 5, "");
_Static_assert(sizeof(struct C2) == 8, "");
#else
_Static_assert(sizeof(struct C1) == 8, "");
_Static_assert(sizeof(struct C2) == 5, "");
#endif

int main()
{
  return 0;
}
