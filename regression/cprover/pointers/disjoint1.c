int unrelated = 123;

int main()
{
  char *output;

  __CPROVER_assume(__CPROVER_w_ok(output));
  __CPROVER_assume(!__CPROVER_same_object(output, &unrelated));
  *output = 'x';

  __CPROVER_assert(unrelated == 123, "property 1");
}
