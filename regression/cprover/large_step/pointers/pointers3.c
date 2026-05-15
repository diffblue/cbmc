int main()
{
  int *p;
  __CPROVER_assume(*p == 10);
  __CPROVER_assert(*p == 10, "property 1"); // passes
}
