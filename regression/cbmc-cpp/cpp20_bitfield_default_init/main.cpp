struct S
{
  unsigned x : 1 = 0;
  unsigned y : 3 = 5;
  int z : 8 = -1;
};

int main()
{
  S s;
  __CPROVER_assert(s.x == 0, "x default");
  __CPROVER_assert(s.y == 5, "y default");
  __CPROVER_assert(s.z == -1, "z default");
  return 0;
}
