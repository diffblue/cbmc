#include <assert.h>
#include <string.h>

int main()
{
  assert(__builtin_memcmp("abc", "abc", 3) == 0);
  assert(__builtin_memcmp("abc", "abd", 3) < 0);
  assert(__builtin_memcmp("abd", "abc", 3) > 0);
  assert(__builtin_memcmp("abc", "abd", 2) == 0);
  return 0;
}
