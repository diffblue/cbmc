#include <assert.h>

enum my_enum
{
  first,
  second,
  third,
  fourth,
  fifth
};

void testfun(enum my_enum ee)
{
}

int main()
{
  enum my_enum ev1;
  enum my_enum ev2;
  __CPROVER_assume(__CPROVER_enum_is_in_range(ev1));
  enum my_enum ev3 = ev1;
  testfun(ev3);
  testfun(ev2);
  return 0;
}
