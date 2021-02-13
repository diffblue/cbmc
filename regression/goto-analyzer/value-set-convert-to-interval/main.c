#include <stdbool.h>

extern int x;

int main(void)
{
  int a = 0;
  int b = 20;
  switch(x)
  {
  case 1:
    a = 1;
    b = 21;
    break;
  case 2:
    a = 2;
    b = 22;
    break;
  case 3:
    a = 3;
    b = 23;
    break;
  case 4:
    a = 4;
    b = 24;
    break;
  case 5:
    a = 5;
    break;
  case 6:
    a = 6;
    break;
  }

  int c = a + b;

  return 0;
}
