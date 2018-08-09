#include <stdlib.h>

struct my_struct
{
  int *field1;
  int *field2;
};

void example(struct my_struct *s)
{
  s->field2 = malloc(sizeof(*(s->field2)));
}

int main()
{
  struct my_struct *s;
  __CPROVER_assume(__CPROVER_points_to_valid_memory(s));
  example(s);
  __CPROVER_assert(__CPROVER_points_to_valid_memory(s->field2), "");
  return 0;
}
