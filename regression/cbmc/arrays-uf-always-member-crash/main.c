struct S
{
  int a[1];
};

int main()
{
  struct S x[2];
  int i;
  __CPROVER_assume(i >= 0 && i < 2);
  __CPROVER_assert(x[i].a[0] == 0, "");
}
