// GCC nested functions: verification of variable capture and calls
int main()
{
  int outer = 10;

  int add(int x)
  {
    return x + outer;
  }

  int multiply(int x)
  {
    return x * outer;
  }

  // basic call and variable capture
  __CPROVER_assert(add(5) == 15, "add(5) == 15");
  __CPROVER_assert(multiply(3) == 30, "multiply(3) == 30");

  // mutation of captured variable is visible
  outer = 20;
  __CPROVER_assert(add(5) == 25, "add(5) == 25 after mutation");

  // nested function used via function pointer
  int (*fp)(int) = &add;
  __CPROVER_assert(fp(1) == 21, "fp(1) == 21");

  // nondet argument
  int n;
  __CPROVER_assume(n >= 0 && n <= 100);
  int r = add(n);
  __CPROVER_assert(r >= 20 && r <= 120, "add(n) in range");

  return 0;
}
