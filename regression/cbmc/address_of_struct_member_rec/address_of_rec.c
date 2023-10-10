struct aux
{
  char comment;
};

struct expr
{
  int line;
  struct aux *info;
};

int main(void)
{
  struct aux info1 = {'a'};
  struct aux info2 = {'b'};
  struct expr var_expr = {42, &info1};
  struct expr other_expr = {34, &info2};
  unsigned int nondet;
  char *ref;
  if(nondet)
    ref = &var_expr.info->comment;
  else
    ref = &other_expr.info->comment;
  __CPROVER_assert(*ref != 'b', "expected failure: ref == 'b'");
  return 0;
}
