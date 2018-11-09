#include <assert.h>
#include <process.h>

int main()
{
  _beginthreadex();
  assert(0);
  return 0;
}
