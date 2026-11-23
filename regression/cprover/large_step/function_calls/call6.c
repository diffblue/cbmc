int my_function(int parameter1, int parameter2)
{
  return parameter1 + parameter2;
}

int main()
{
  int x;
  x = my_function(123, 1);
  __CPROVER_assert(x == 124, "property 1"); // should pass
}
