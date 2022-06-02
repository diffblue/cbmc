#include <stdlib.h>

int main()
{
  int *p = nondet() ? malloc(10) : malloc(20);
}
