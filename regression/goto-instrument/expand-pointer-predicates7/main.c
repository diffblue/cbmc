#include <stdlib.h>

struct my_struct
{
  int *field;
};

void example(struct my_struct *s)
{
  __CPROVER_assume(__CPROVER_points_to_valid_memory(s));
  size_t size;
  __CPROVER_assume(size == sizeof(*(s->field)));
  __CPROVER_assume(__CPROVER_points_to_valid_memory(s->field, size));
  int read = *(s->field);
}

int main()
{
  struct my_struct *s;
  example(s);
  return 0;
}
