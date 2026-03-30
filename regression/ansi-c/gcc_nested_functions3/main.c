// Test multiple nested function calls and interactions
int main()
{
  int base = 5;

  int add(int x)
  {
    return x + base;
  }

  int multiply(int x)
  {
    return x * base;
  }

  int result1 = add(10);
  int result2 = multiply(4);

  __CPROVER_assert(result1 == 15, "add should work");
  __CPROVER_assert(result2 == 20, "multiply should work");

  return 0;
}
