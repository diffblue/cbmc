int global;

int main()
{
  int *x;
  __CPROVER_assume(__CPROVER_w_ok(x));
  *x = 123;
  __CPROVER_assert(global == 0, "property 1");
}
