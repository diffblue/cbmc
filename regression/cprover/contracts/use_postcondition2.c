int global;

void callee() __CPROVER_ensures(global >= 10) __CPROVER_assigns(global)
{
  global = 20;
}

int main()
{
  global = 1;
  callee();
  __CPROVER_assert(0, "property 1"); // should fail
  return 0;
}
