#include <assert.h>
#include <new.h>

int main()
{
  __delete();
  assert(0);
  return 0;
}
