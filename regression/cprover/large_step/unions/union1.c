union U
{
  int i;
  char ch;
};

int main()
{
  union U u;

  u.i = 1;
  __CPROVER_assert(u.i == 1, "property 1"); // passes

  u.ch = 2;
  __CPROVER_assert(u.ch == 2, "property 2"); // passes

  return 0;
}
