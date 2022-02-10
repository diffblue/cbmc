struct empty
{
};

struct non_empty
{
  int x;
};

union U
{
  struct empty e;
  struct non_empty n;
};

int main()
{
  union U u;
  struct empty e = u.e;
  __CPROVER_assert(0, "dummy assertion");
}
