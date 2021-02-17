#include <assert.h>

enum my_enum
{
  first,
  second,
  third,
  fourth,
  fifth
};

int main()
{
  enum my_enum ev1;
  enum my_enum ev2;
  ev1 = first;
  ev2 = fifth;
  int i = 0;
  while(i < 10)
  {
    ev1++;
    assert(__CPROVER_enum_is_in_range(i));
    i++;
  }
  return 0;
}
