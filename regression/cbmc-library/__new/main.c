#include <assert.h>
#include <new.h>

int main()
{
  __new();
  assert(0);
  return 0;
}
