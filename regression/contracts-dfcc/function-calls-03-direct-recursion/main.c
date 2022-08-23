int f(int *x) __CPROVER_assigns() __CPROVER_requires(0 <= *x)
  __CPROVER_ensures(__CPROVER_return_value == *x)
{
  if(*x < 1)
    return 0;
  int loc = *x - 1;   // subtract 1
  return f(&loc) + 1; // add 1, cancels out
}

int nondet_int();
int main()
{
  int x = nondet_int();
  __CPROVER_assume(0 <= x);
  f(&x);
  return 0;
}
