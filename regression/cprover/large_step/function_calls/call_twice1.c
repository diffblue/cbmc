int global;

void my_function()
{
  global++; // a side effect
}

int main()
{
  global = 1;
  my_function();
  __CPROVER_assert(global == 2, "property 1"); // should pass

  my_function();
  __CPROVER_assert(global == 3, "property 2"); // should pass
}
