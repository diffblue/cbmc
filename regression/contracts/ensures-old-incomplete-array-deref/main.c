// `p` points to an incomplete array type. The ensures clause captures the
// pre-state value via __CPROVER_old((*p)[i]); building that history variable
// runs all_dereferences_are_valid (goto-instrument/contracts/utils.cpp) over
// the dereference *p. size_of_expr() has no value for the incomplete array
// element, so this exercises the minimal-size fall-back rather than crashing.
int (*p)[];

int foo(int i)
  // clang-format off
  __CPROVER_ensures(__CPROVER_return_value == __CPROVER_old((*p)[i]))
// clang-format on
{
  return (*p)[i];
}

int main()
{
  int i;
  foo(i);
  return 0;
}
