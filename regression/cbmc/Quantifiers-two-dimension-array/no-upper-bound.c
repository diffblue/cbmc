int main()
{
  int a[2][2];

  __CPROVER_assume(__CPROVER_forall {
    unsigned i;
    __CPROVER_forall
    {
      unsigned j;
      a[i % 2][j % 2] == (i % 2) + (j % 2)
    }
  });

  assert(a[0][0] == 0);
  assert(a[0][1] == 1);
  assert(a[1][0] == 1);
  assert(a[1][1] == 2);

  return 0;
}
