#include <assert.h>
#include <new.h>

int main()
{
  __delete_array();
  assert(0);
  return 0;
}
