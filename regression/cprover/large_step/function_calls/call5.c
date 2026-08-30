int my_function(int parameter)
{
  return parameter;
}

int main()
{
  int x;
  x = my_function(123);
  __CPROVER_assert(x == 123, "property 1"); // should pass
}
