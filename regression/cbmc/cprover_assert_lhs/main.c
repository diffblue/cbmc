int main()
{
  void m = __CPROVER_assert("n>5", "foo");

  return 0;
}
