// Test for issue #8200: cast-to-pointer should not miss error
// (char*)0x55a8a2e6b007 could equal x's address
#include <assert.h>
int main()
{
  char *x = "";
  char *ptr = (char *)0x55a8a2e6b007;
  assert(ptr != x);
}
