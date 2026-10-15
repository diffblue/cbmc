// Exercises value-set simplification of function-call arguments in
// goto_symext::symex_function_call: each argument expression below is a pointer
// dereference / pointer comparison that is L2-renamed and then value-set
// simplified before being recorded as an SSA function_call step. The
// assertions check that the argument values are preserved through that
// simplification.

void check_value(int x)
{
  __CPROVER_assert(x == 42, "dereferenced argument value preserved");
}

void check_flag(int b)
{
  __CPROVER_assert(b, "pointer-comparison argument preserved");
}

int main()
{
  int a = 42;
  int *p = &a;
  int **pp = &p;

  // doubly-indirect dereference passed as an argument
  check_value(**pp);

  // pointer comparison passed as an argument
  check_flag(p == &a);

  return 0;
}
