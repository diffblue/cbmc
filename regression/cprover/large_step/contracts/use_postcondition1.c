int global;

void callee() __CPROVER_ensures(global >= 10) __CPROVER_assigns(global)
{
  global = 20;
}

int main()
{
  callee();
  __CPROVER_assert(global >= 10, "property 1");
  return 0;
}
