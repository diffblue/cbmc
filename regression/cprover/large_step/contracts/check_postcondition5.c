void my_function(int *in, int *out) __CPROVER_requires(__CPROVER_rw_ok(in))
  __CPROVER_requires(__CPROVER_rw_ok(out))
    __CPROVER_requires(!__CPROVER_same_object(in, out))
      __CPROVER_assigns(*in, *out) __CPROVER_ensures(*out == __CPROVER_old(*in))
{
  *out = *in;
  *in = 0; // overwrite
}
