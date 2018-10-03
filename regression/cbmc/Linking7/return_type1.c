#include <assert.h>

struct S
{
  int i;
};

struct S *function();

int main()
{
  assert(function() != 0);
}
