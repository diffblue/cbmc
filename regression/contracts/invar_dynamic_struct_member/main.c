typedef struct test
{
  int x;
} test;

void main()
{
  struct test *t = malloc(sizeof(test));
  t->x = 0;

  unsigned n;
  for(unsigned i = 0; i < n; ++i)
    __CPROVER_loop_invariant(i <= n)
    {
      switch(i % 4)
      {
      case 0:
        break;

      case 1:
      case 2:
        t->x += 1;

      default:
        t->x += 2;
      }
    }

  assert(t->x == 0 || t->x == 1 || t->x == 2);
}
