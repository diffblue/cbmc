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
  assert(__CPROVER_enum_is_in_range(ev1, ev2));
  return 0;
}
