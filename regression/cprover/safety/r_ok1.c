int main()
{
  int *p;
  __CPROVER_assume(__CPROVER_r_ok(p));
  *p;       // safe
  *(p + 1); // unsafe

  return 0;
}
