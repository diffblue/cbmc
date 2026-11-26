int nondet_int(void);
int main()
{
  int a[4];
  int n = nondet_int();
  __CPROVER_assume(0 < n && n <= 4);
  __CPROVER_bool b = __CPROVER_exists
  {
    int j;
    (0 <= j && j < n) && a[j] == 7
  };
  int x = b ? 1 : 0;
  __CPROVER_assert(x == 0, "can find 7");
  __CPROVER_bool c = __CPROVER_forall
  {
    int j;
    !(0 <= j && j < n) || a[j] == 7
  };
  __CPROVER_assert(c != b, "differ");
  return 0;
}
