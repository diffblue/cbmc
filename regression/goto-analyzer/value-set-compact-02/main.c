#include <stdbool.h>

extern int x;

int main(void)
{
  int a[1] = {0};
  switch(x)
  {
  case 1:
    a[0] = 1;
    break;
  case 2:
    a[0] = 2;
    break;
  case 3:
    a[0] = 3;
    break;
  case 4:
    a[0] = 4;
    break;
  case 5:
    a[0] = 5;
    break;
  case 6:
    a[0] = 6;
    break;
  case 7:
    a[0] = 7;
    break;
  case 8:
    a[0] = 8;
    break;
  case 9:
    a[0] = 9;
    break;
  case 10:
    a[0] = 10;
    break;
  case 11:
    a[0] = 11;
    break;
  case 12:
    a[0] = 12;
    break;
  }

  return 0;
}
