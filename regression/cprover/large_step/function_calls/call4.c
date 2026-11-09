int global;

void my_function()
{
  global = 10; // a side effect
}

int main()
{
  my_function();
  __CPROVER_assert(global == 10, "property 1"); // should pass
}
