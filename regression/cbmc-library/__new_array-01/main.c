#include <assert.h>
#include <new.h>

int main()
{
  __new_array();
  assert(0);
  return 0;
}
