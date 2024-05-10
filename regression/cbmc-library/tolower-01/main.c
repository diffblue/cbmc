#include <assert.h>
#include <ctype.h>

int main()
{
  int x;
  int r = tolower(x);
  assert(r >= x);
  return 0;
}
