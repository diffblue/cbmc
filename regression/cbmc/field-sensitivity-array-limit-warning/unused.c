// Over-limit arrays that are never indexed lose nothing by being tracked as a
// whole, so they are not reported.
struct s
{
  int *p;
  int x;
};

struct s unused_global[100];
struct s used_global[100];

void f(void)
{
  struct s unused_local[100];
}

int main(void)
{
  int x;
  used_global[3].p = &x;
  f();
  __CPROVER_assert(used_global[3].p == &x, "used");
  return 0;
}
