#include <cassert>

int main()
{
  int *some_data = new int(10);
  assert(some_data);
  assert(*some_data == 10);
  return 0;
}
