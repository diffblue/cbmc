#include "first_one.h"

int another(int (*fun_ptr)(int), int c)
{
  int a = (*fun_ptr)(c);

  return a;
}
