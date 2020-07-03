#include <stdbool.h>

extern int x;

int main(void)
{
  bool b1;
  bool b2;

  b1 = true;
  b2 = !b1;

  bool b3;
  if(x)
    b3 = true;
  else
    b3 = false;

  int i = b3 ? 10 : 20;

  return 0;
}
