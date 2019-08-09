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
  enum day temp = 100;
  printf("%d\n", temp);
  return 0;
}
