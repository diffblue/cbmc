#include <assert.h>

int g, k;

// GCC's `a ? : b` (omitted middle operand) evaluates `a` exactly once at run
// time, but in a constant context there are no side effects, so it must fold
// to `(a != 0) ? a : b`.  The constant-context form is the Linux kernel
// cache-line alignment pattern: __cacheline_group_begin_aligned expands to
// __attribute__((aligned((__VA_ARGS__ + 0) ? : SMP_CACHE_BYTES))).

// --- constant contexts: the value must fold at compile time ---

// aligned attribute (folded via make_constant)
struct zero_cond
{
  int a;
  int grp __attribute__((aligned((0 + 0) ?: 64))); // 0 ?: 64 -> aligned 64
};

struct nonzero_cond
{
  int a;
  int grp __attribute__((aligned((16 + 0) ?: 64))); // 16 ?: 64 -> aligned 16
};

// array dimensions: make the folded value observable -- a wrong fold yields a
// negative dimension and fails the build
int check_nonzero[((16 + 0) ?: 64) == 16 ? 1 : -1];
int check_zero[((0 + 0) ?: 64) == 64 ? 1 : -1];

// enum values fold via their own path (typecheck_c_enum_type)
enum e
{
  enum_zero = (0 ?: 64),    // -> 64
  enum_nonzero = (16 ?: 64) // -> 16
};
int check_enum_zero[enum_zero == 64 ? 1 : -1];
int check_enum_nonzero[enum_nonzero == 16 ? 1 : -1];

// See https://gcc.gnu.org/onlinedocs/gcc/Conditionals.html
int main()
{
  // --- run-time contexts: `a` is evaluated exactly once ---
  int r1, r2;

  r1= (g++) ? : 2;

  assert(r1==2);
  assert(g==1);

  r2= (g++) ? : (k++);

  assert(r2==1);
  assert(g==2);
  assert(k==0);

  int in_decl = g++ ?: 0;
  assert(in_decl == 2);
  assert(g == 3);

  return 0;
}
