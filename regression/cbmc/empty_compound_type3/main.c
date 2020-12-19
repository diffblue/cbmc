#include <string.h>

struct a
{
} b()
{
  struct a *c;
  memcpy(c + 2, c, 1);
}
int main()
{
  b();
}
