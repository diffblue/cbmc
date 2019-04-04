struct S
{
  int v;
  struct Inner
  {
    int x;
  } inner;
};

struct S works;

int main()
{
  struct S fails;

  works.v = 2;
  fails.v = 2;

  while(works.v > 0)
    --(works.v);

  while(fails.v > 0)
    --(fails.v);

  __CPROVER_assert(works.inner.x == 0, "");

  _Bool b;
  if(b)
  {
    struct S s = {42, {42}};
  }

  return 0;
}
