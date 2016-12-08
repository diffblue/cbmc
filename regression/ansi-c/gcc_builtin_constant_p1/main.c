#include <assert.h>

enum { E1=1 } var;

struct whatnot
{
} whatnot_var;

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

  // side-effects are _not_ evaluated
  int i=0;
  assert(!__builtin_constant_p(i++));
  assert(i==0);
  #endif
}
