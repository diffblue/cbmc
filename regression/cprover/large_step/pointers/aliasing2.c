int main()
{
  int *in, *out;
  __CPROVER_assume(__CPROVER_rw_ok(in) && __CPROVER_rw_ok(out));
  __CPROVER_assume(!__CPROVER_same_object(in, out));
  int old_in = *in;

  *out = *in;
  *in = 0; // overwrite

  __CPROVER_assert(*out == old_in, "property 1");
}
