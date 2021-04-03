int *bar(int *unmodified, int *modifed);

int main()
{
  int x = 3;
  int y = 4;
  int *p2x = &x;
  p2x = bar(&x, &y);
  __CPROVER_assert(y == 5, "assertion y == 5");
  __CPROVER_assert(p2x == &y, "assertion p2x == &y");
  __CPROVER_assert(*p2x == 5, "assertion *p2x == 5");
}

int *bar(int *unmodified, int *modifed)
{
  __CPROVER_assert(*unmodified == 3, "assertion *unmodified == 3");

  (*modifed) += 1;

  __CPROVER_assert(*modifed == 5, "assertion *modifed == 5");

  return modifed;
}
