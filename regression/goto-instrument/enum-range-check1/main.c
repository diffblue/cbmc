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
  enum day temp = friday;
  temp = sunday;
  temp = monday;
  temp = tuesday;
  temp = wednesday;
  temp = thursday;
  temp = thursday + 1;
  temp = saturday;
  printf("%d\n", temp);
  return 0;
}
