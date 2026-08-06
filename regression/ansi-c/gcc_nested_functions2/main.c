// Test nested function with auto keyword and forward declaration
int main()
{
  int outer_var = 20;

  // Forward declaration with auto keyword
  auto int nested_func(int x);

  // Nested function definition
  int nested_func(int x)
  {
    return x * outer_var;
  }

  int result = nested_func(3);
  __CPROVER_assert(
    result == 60, "nested function should access outer variable");

  return 0;
}
