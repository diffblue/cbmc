#include <assert.h>
#include <string.h>

int main()
{
  char d[4];
  char *r = strcpy(d, "abc");
  assert(r == d);
  assert(strlen(d) == 3);
  return 0;
}
