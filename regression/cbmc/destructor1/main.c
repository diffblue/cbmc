#include <assert.h>

#ifdef __GNUC__
// Will be implicitly invoked after main() completes if the attribute is
// properly supported
__attribute__((destructor))
#endif
void assert_false(void)
{
  assert(0);
}

int main()
{
#ifndef __GNUC__
  // explicitly invoke assert_false as __attribute__((destructor)) isn't
  // supported in non-GCC modes
  assert_false();
#endif
}
