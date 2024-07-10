#include <assert.h>

#ifdef __GNUC__
enum
{
  E1 = 1
} var;

struct whatnot
{
} whatnot_var;
#endif

int main()
{
  // this is gcc only

#ifdef __GNUC__
  assert(__builtin_constant_p("some string"));
  assert(__builtin_constant_p(1.0f));
  assert(__builtin_constant_p(E1));
  assert(!__builtin_constant_p(var));
  assert(!__builtin_constant_p(main));
  assert(!__builtin_constant_p(whatnot_var));
  assert(!__builtin_constant_p(&var));
  assert(__builtin_constant_p(__builtin_constant_p(var)));

  // The following are not constant expressions in the sense of the C standard
  // and GCC wouldn't deem them constant expressions either, but they are
  // subject to GCC's constant folding. See also regression test ansi-c/sizeof6.
  // Clang's behaviour, however, is somewhat different. See
  // https://github.com/llvm/llvm-project/issues/55946 for further examples of
  // where they differ.
  int j;
#  ifndef __clang__
  assert(__builtin_constant_p(j * 0));
  assert(__builtin_constant_p(j - j));
  assert(__builtin_constant_p(j ? 0ll : 0ll));
#  endif
  assert(__builtin_constant_p(0 ? j : 0ll));

  // side-effects are _not_ evaluated
  int i = 0;
  assert(!__builtin_constant_p(i++));
  assert(i == 0);
#endif
}
