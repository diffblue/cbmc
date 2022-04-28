int main()
{
  int a = 10;
  int *b = &a;
  int c;

  *b = 12;

  __CPROVER_assert(a != *b, "a should be different than b");
  __CPROVER_assert(a == *b, "a should not be different than b");
  __CPROVER_assert(
    *b != c,
    "c can get assigned a value that makes it the same what b points to");
}
