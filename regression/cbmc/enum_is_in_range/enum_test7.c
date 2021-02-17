#include <assert.h>

typedef enum
{
  first,
  second,
  third,
  fourth,
  fifth
} my_enum;

int main()
{
  my_enum ev1;
  my_enum ev2;
  ev1 = first;
  ev2 = fifth;
  while(!(ev1 == ev2))
  {
    ev1++;
    assert(__CPROVER_enum_is_in_range(ev1));
  }
  return 0;
}
