#include <assert.h>
#include <string.h>

int main()
{
  assert(__builtin_strcmp("abc", "abc") == 0);
  assert(__builtin_strcmp("abc", "abd") < 0);
  assert(__builtin_strcmp("abd", "abc") > 0);
  return 0;
}
