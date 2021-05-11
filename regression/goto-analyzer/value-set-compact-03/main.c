#include <stdbool.h>

extern int x;

struct S
{
  int a;
};

int main(void)
{
  struct S a;
  a.a = 0;
  switch(x)
  {
  case 1:
    a.a = 1;
    break;
  case 2:
    a.a = 2;
    break;
  case 3:
    a.a = 3;
    break;
  case 4:
    a.a = 4;
    break;
  case 5:
    a.a = 5;
    break;
  case 6:
    a.a = 6;
    break;
  case 7:
    a.a = 7;
    break;
  case 8:
    a.a = 8;
    break;
  case 9:
    a.a = 9;
    break;
  case 10:
    a.a = 10;
    break;
  case 11:
    a.a = 11;
    break;
  case 12:
    a.a = 12;
    break;
  }

  return 0;
}
