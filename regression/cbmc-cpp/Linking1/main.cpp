#include "module.h"
#include <cassert>

extern int i;

int main()
{
  assert(i == 1);

  T t;
  t.f();

  assert(i == 2);
}
