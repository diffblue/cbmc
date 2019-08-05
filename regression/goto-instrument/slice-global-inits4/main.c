struct S
{
  int x;
};

struct T
{
  struct S *s;
};

int main()
{
  static struct S s = {42};
  static struct T t = {.s = &s};
  __CPROVER_assert(t.s->x == 42, "must be 42");
}
