union U
{
  int i;
  char ch;
};

int main()
{
  union U u;

  u.i = 0;
  u.ch = 1;
  __CPROVER_assert(u.i == 1, "property 1"); // passes on little endian

  return 0;
}
