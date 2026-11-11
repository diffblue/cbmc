struct A
{
  char c;
};

struct S
{
  union
  {
    struct A *p;
  } u;
};

struct S s2;

char get_module_value(void)
{
  static struct A a = {'c'};
  s2.u.p = &a;
  return s2.u.p->c;
}
