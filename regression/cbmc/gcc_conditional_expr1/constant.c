// GCC's `a ? : b` (omitted middle operand) evaluates `a` exactly once at run
// time (see main.c), but in a constant context there are no side effects, so
// it must fold to `(a != 0) ? a : b`.

// The Linux kernel's cache-line alignment pattern, where the alignment is
// `0 ? : 64` when no explicit alignment is given.
#define SMP_CACHE_BYTES 64
#define __aligned(x) __attribute__((__aligned__(x)))
#define __cacheline_group_begin_aligned(GROUP, ...)                            \
  unsigned char __cacheline_group_begin__##GROUP[0] __aligned(                 \
    (__VA_ARGS__ + 0) ?: SMP_CACHE_BYTES)

struct cachelines
{
  int a;
  __cacheline_group_begin_aligned(default_alignment); // aligned to 64
  int b;
  __cacheline_group_begin_aligned(explicit_alignment, 16); // aligned to 16
  int c;
};

// Array dimensions and static assertions make the folded values observable at
// compile time: a wrong fold yields a negative dimension or a failed
// assertion.
int check_nonzero[((16 + 0) ?: 64) == 16 ? 1 : -1];
int check_zero[((0 + 0) ?: 64) == 64 ? 1 : -1];
_Static_assert((0 ?: (0 ?: 7)) == 7, "nested");

// Enum values and bit-field widths are folded by their own code paths.
enum e
{
  enum_zero = (0 ?: 64),
  enum_nonzero = (16 ?: 64)
};
int check_enum_zero[enum_zero == 64 ? 1 : -1];
int check_enum_nonzero[enum_nonzero == 16 ? 1 : -1];

struct bit_fields
{
  unsigned zero : (0 ?: 3);
  unsigned nonzero : (2 ?: 7);
};

int main(int argc, char *argv[])
{
  __CPROVER_assert(
    __builtin_offsetof(
      struct cachelines, __cacheline_group_begin__default_alignment) == 64,
    "0 ?: 64 aligns to 64");
  __CPROVER_assert(
    __builtin_offsetof(
      struct cachelines, __cacheline_group_begin__explicit_alignment) == 80,
    "16 ?: 64 aligns to 16");

  struct bit_fields bf;
  bf.zero = 7;
  bf.nonzero = 7;
  __CPROVER_assert(bf.zero == 7 && bf.nonzero == 3, "bit-field widths");

  // case labels are folded via make_constant
  switch(argc)
  {
  case(0 ?: 1):
    break;
  case(2 ?: 3):
    break;
  }

  return 0;
}
