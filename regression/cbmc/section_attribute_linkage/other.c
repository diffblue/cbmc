#include "other.h"

struct point p __attribute__((section("foo")));

int get()
{
  return p.x;
}
