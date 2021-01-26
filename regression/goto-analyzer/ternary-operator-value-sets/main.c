#include <stdbool.h>

extern int x;

int main(void)
{
  bool b1;
  bool b2;

  b1 = true;
  b2 = !b1;

  bool b3 = x ? true : false;
  int i = b1 ? 10 : 20;
  int j = b2 ? 10 : 20;
  int k = b3 ? 10 : 20;

  return 0;
}
