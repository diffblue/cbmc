#include <assert.h>

// struct A differs from the one in module.c, which makes the linker rename
// struct A and struct S of one of the two files. The anonymous union nested in
// struct S depends on struct A, but its name already reflects the body of
// struct A, so that its new name is the same as its old one.
struct A
{
  int x;
};

struct S
{
  union
  {
    struct A *p;
  } u;
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
