int my_function(int *p)
{
  return *p;
}

int main()
{
  int x, y;
  x = my_function(&y);
  __CPROVER_assert(x == y, "property 1"); // should pass
}
