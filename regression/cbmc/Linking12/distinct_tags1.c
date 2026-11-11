struct A
{
  int x;
};

struct S
{
  union
  {
    struct A *p;
    int *q;
  } u;
};

int get(struct S *s);

int main(void)
{
  struct A a = {7};
  struct S s;
  s.u.p = &a;
  __CPROVER_assert(get(&s) == 7, "x");
  return 0;
}
