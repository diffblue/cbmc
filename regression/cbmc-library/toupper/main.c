#include <assert.h>
#include <ctype.h>

int main()
{
  int x;
  int r = toupper(x);
  assert(r <= x);
  return 0;
}
