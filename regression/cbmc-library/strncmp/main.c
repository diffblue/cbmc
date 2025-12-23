#include <assert.h>
#include <string.h>

#include <assert.h>
#include <string.h>

int main()
{
  char a[] = "abc";
  char b[] = "xyz";
  assert(strncmp(a, b, 0) == 0);
  assert(strncmp(a, b, 1) == -1);
  assert(strncmp(b, a, 1) == 1);
  return 0;
}
