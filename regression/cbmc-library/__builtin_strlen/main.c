#include <assert.h>
#include <string.h>

int main()
{
  assert(__builtin_strlen("abc") == 3);
  return 0;
}
