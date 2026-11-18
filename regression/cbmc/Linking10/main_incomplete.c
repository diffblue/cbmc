#include <assert.h>

// struct A is incomplete where the anonymous union is declared, and its body
// differs from the one in module_incomplete.c: the linker renames the
// anonymous union of module_incomplete.c, as its name then has to reflect the
// body of struct A
struct A;

struct S
{
  union
  {
    struct A *p;
  } u;
};

struct A
{
  int x;
};

struct S s1;

char get_module_value(void);

int main(void)
{
  struct A a = {42};
  s1.u.p = &a;
  assert(s1.u.p->x == 42);
  assert(get_module_value() == 'c');
  return 0;
}
