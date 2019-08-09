#include <stdio.h>

enum day
{
  sunday = 1,
  monday,
  tuesday = 5,
  wednesday,
  thursday = 10,
  friday,
  saturday
};

int main()
{
#pragma CPROVER check push
#pragma CPROVER check disable "enum-range"
  enum day temp = 100;
  printf("%d\n", temp);
#pragma CPROVER check pop
  return 0;
}
