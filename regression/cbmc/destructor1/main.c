#include <assert.h>

#ifdef __GNUC__
static __attribute__((destructor)) void assert_false(void)
{
  assert(0);
}
#endif

int main()
{
#ifndef __GNUC__
  // explicitly invoke assert_false as __attribute__((destructor)) isn't
  // supported
  assert_false();
#endif
}
