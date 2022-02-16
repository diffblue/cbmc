void main(void)
{
  // HAVOC through nondet conditional
  typedef struct
  {
    int i;
    int j;
  } st;
  int i = 10;
  int old_i = 10;
  st s = {20, 30};
  st old_s = s;

  _Bool c;

  int *p = c ? &i : &s.i;

  __CPROVER_havoc_slice(p, sizeof(*p));

  if(c)
  {
    __CPROVER_assert(i == old_i, "expecting FAILURE");
    __CPROVER_assert(s.i == old_s.i, "expecting SUCCESS");
    __CPROVER_assert(s.j == old_s.j, "expecting SUCCESS");
  }
  else
  {
    __CPROVER_assert(i == old_i, "expecting SUCCESS");
    __CPROVER_assert(s.i == old_s.i, "expecting FAILURE");
    __CPROVER_assert(s.j == old_s.j, "expecting SUCCESS");
  }

  return;
}
