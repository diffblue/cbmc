#include <stdint.h>

// Member-level alignment is context-dependent: an aligned() attribute on a
// member can only *increase* the alignment in a non-packed struct, but inside
// a packed struct it is honoured verbatim (and may reduce the alignment). The
// enclosing struct's alignment and size follow from the resulting member
// alignments. These values match GCC and Clang.

struct NPInner
{
  uint8_t c;
  int32_t i;
};

typedef struct __attribute__((packed)) PInner
{
  uint8_t c;
  int32_t i;
} PInner_t;

// non-packed struct, member aligned(2) < natural 4: the request is ignored
struct M_a2
{
  uint8_t c;
  int32_t __attribute__((aligned(2))) m;
};

// non-packed struct, member aligned(8) > natural: honoured
struct M_a8
{
  uint8_t c;
  int32_t __attribute__((aligned(8))) m;
};

// packed struct, member aligned(2): honoured verbatim (reduces below natural)
struct __attribute__((packed)) PM_a2
{
  uint8_t c;
  int32_t __attribute__((aligned(2))) m;
};

// packed struct, member aligned(8): honoured, raising the struct alignment
struct __attribute__((packed)) PM_a8
{
  uint8_t c;
  int32_t __attribute__((aligned(8))) m;
};

// non-packed struct, struct-level aligned(2) < natural: ignored
struct __attribute__((aligned(2))) S_a2
{
  int32_t i;
};

// a typedef requesting an alignment smaller than natural: honoured for the
// type itself (this is the one place aligned() may reduce a scalar alignment)
typedef int32_t __attribute__((aligned(2))) ai2_t;

// packed-struct-typedef member with an aligned() attribute
struct Outer
{
  uint8_t c;
  PInner_t __attribute__((aligned(8))) inner;
};

int main(void)
{
  _Static_assert(sizeof(struct M_a2) == 8, "");
  _Static_assert(_Alignof(struct M_a2) == 4, "");

  _Static_assert(sizeof(struct M_a8) == 16, "");
  _Static_assert(_Alignof(struct M_a8) == 8, "");

  _Static_assert(sizeof(struct PM_a2) == 6, "");
  _Static_assert(_Alignof(struct PM_a2) == 2, "");

  _Static_assert(sizeof(struct PM_a8) == 16, "");
  _Static_assert(_Alignof(struct PM_a8) == 8, "");

  _Static_assert(sizeof(struct S_a2) == 4, "");
  _Static_assert(_Alignof(struct S_a2) == 4, "");

  _Static_assert(sizeof(ai2_t) == 4, "");
  _Static_assert(_Alignof(ai2_t) == 2, "");

  _Static_assert(sizeof(struct Outer) == 16, "");
  _Static_assert(_Alignof(struct Outer) == 8, "");
  _Static_assert(__builtin_offsetof(struct Outer, inner) == 8, "");

  return 0;
}
