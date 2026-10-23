#include <stdint.h>

// Union tail-padding and alignment must match GCC/Clang.

// A plain union: size is the largest member, alignment the largest member's.
union U_plain
{
  uint8_t c;
  int32_t i;
};

// A packed union: alignment drops to 1, size stays the largest member.
union __attribute__((packed)) U_packed
{
  uint8_t c;
  int32_t i;
};

// An aligned union: size is padded up to the alignment.
union __attribute__((aligned(16))) U_aligned
{
  uint8_t c;
  int32_t i;
};

// A packed *and* aligned union: the explicit alignment still applies despite
// packing, and the size is padded up to it (this used to yield size 4).
union __attribute__((packed)) __attribute__((aligned(16))) U_pa
{
  uint8_t c;
  int32_t i;
};

// Member-level aligned() on a packed-struct-typedef member: the member (and
// hence the enclosing struct) is aligned as requested while the inner packing
// is preserved.
typedef struct __attribute__((packed)) Inner
{
  uint8_t c;
  int32_t i;
} Inner_t;

struct Outer
{
  uint8_t c;
  Inner_t __attribute__((aligned(8))) inner;
};

int main(void)
{
  _Static_assert(sizeof(union U_plain) == 4, "");
  _Static_assert(_Alignof(union U_plain) == 4, "");

  _Static_assert(sizeof(union U_packed) == 4, "");
  _Static_assert(_Alignof(union U_packed) == 1, "");

  _Static_assert(sizeof(union U_aligned) == 16, "");
  _Static_assert(_Alignof(union U_aligned) == 16, "");

  _Static_assert(sizeof(union U_pa) == 16, "");
  _Static_assert(_Alignof(union U_pa) == 16, "");

  _Static_assert(sizeof(Inner_t) == 5, "");
  _Static_assert(_Alignof(Inner_t) == 1, "");

  _Static_assert(sizeof(struct Outer) == 16, "");
  _Static_assert(_Alignof(struct Outer) == 8, "");
  _Static_assert(__builtin_offsetof(struct Outer, inner) == 8, "");

  return 0;
}
