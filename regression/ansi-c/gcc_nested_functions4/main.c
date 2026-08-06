// Test taking address of nested function (if supported)
int main()
{
  int multiplier = 3;

  int multiply_by(int x)
  {
    return x * multiplier;
  }

  // Taking address of nested function
  int (*func_ptr)(int) = multiply_by;

  int result = func_ptr(7);
  __CPROVER_assert(result == 21, "function pointer should work");

  return 0;
}
