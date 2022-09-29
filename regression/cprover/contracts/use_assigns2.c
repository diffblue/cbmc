int global;

void my_function1(void) __CPROVER_assigns(global)
{
}

int main()
{
  global = 1;

  my_function1(); // does assign 'global'

  __CPROVER_assert(global == 1, "property 1"); // fails

  return 0;
}
