int counter;

static void bump(int *p)
{
  *p += 1;
}

int main()
{
  int local = 0;
  bump(&local);
  counter = local + 1;
  __CPROVER_assert(counter == 2, "counter");
  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}
