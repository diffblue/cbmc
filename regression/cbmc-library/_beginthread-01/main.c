#include <assert.h>
#include <process.h>

int main()
{
  _beginthread();
  assert(0);
  return 0;
}
