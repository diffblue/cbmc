void function(int *a);

int main()
{
  int a = 0;
  function(&a);
  __CPROVER_assert(a == 0, "");
  return 0;
}
