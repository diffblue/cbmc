void foo()
{
  int nondet_var;
  int __VERIFIER_var;
  int __CPROVER_var;
  for(int i = 10; i > 0; i--)
    // clang-format off
  __CPROVER_assigns(i,nondet_var, __VERIFIER_var, __CPROVER_var)
  __CPROVER_loop_invariant(0 <= i && i <= 10)
  __CPROVER_decreases(i)
    // clang-format on
    {
      nondet_var = 0;
      __VERIFIER_var = 0;
      __CPROVER_var = 0;
    }
}

int main()
{
  foo();
  return 0;
}
