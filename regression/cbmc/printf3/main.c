#include <assert.h>
#include <stdio.h>

int main()
{
  printf("%ld", 10);
  printf("%llu", 11);
  printf("%hhd", 12);
  printf("%lf", 10.0);
  printf("%Lf", 11.0);
  assert(0);
}
