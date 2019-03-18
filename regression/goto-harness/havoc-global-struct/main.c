#include <assert.h>

struct simple_str
{
  int i;
  int j;
} simple;

void checkpoint()
{
}

int main()
{
  simple.i = 1;
  simple.j = 2;

  checkpoint();
  assert(simple.j > simple.i);
  return 0;
}
