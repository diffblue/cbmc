struct expr
{
  int line;
  char comment;
};

int main(int argc, char *argv[])
{
  struct expr var_expr = {42, 'a'};
  struct expr other_expr = {34, 'b'};
  unsigned int nondet;
  int *ref;
  if(nondet)
    ref = &var_expr.line;
  else
    ref = &other_expr.line;
  __CPROVER_assert(*ref != 34, "expected failure: ref == 34");
  return 0;
}
