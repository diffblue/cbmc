struct S
{
  int x;
};

int main()
{
  unsigned size;
  __CPROVER_assume(size > 0);
  struct S array[size];
  __CPROVER_assert(array[0].x == 0, "not always zero");
}
