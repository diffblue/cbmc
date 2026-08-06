// Test basic nested function definition
int main()
{
  int outer_var = 10;

  // Nested function definition
  int nested_func(int x)
  {
    return x + outer_var;
  }

  int result = nested_func(5);
  __CPROVER_assert(
    result == 15, "nested function should access outer variable");

  return 0;
}
