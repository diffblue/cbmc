extern int undefined_function();

int main()
{
  int nondet1 = undefined_function();
  __CPROVER_assume(nondet1 == 10);
  __CPROVER_assert(nondet1 < 11, "");
  __CPROVER_assert(undefined_function() == 0, "");

  __CPROVER_assert(undefined_function() == undefined_function(), "");
}
