int my_function()
{
  return 10;
}

int main()
{
  int x;
  x = my_function();
  __CPROVER_assert(x == 10, "property 1"); // should pass
}
