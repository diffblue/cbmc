struct S
{
  int x, y;
};

extern struct S some_struct;

int main()
{
  // should fail
  __CPROVER_assert(some_struct.x == some_struct.y, "property 1");
  return 0;
}
