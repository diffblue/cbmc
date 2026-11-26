struct S
{
  signed int s : 6;
  unsigned int u : 6;
};

int nondet_int(void);
int main()
{
  _Bool b = nondet_int() != 0;
  double e = b;
  __CPROVER_assert(e == 0.0 || e == 1.0, "bool to double");
  __CPROVER_assert(b || e == 0.0, "false is zero");
  __CPROVER_assert(e != 1.0, "can be one");

  float m;
  __CPROVER_assume(m == -0.0f);
  _Bool mb = m;
  __CPROVER_assert(!mb, "negative zero is false");
  float h;
  __CPROVER_assume(h == 0.5f);
  _Bool hb = h;
  __CPROVER_assert(hb, "one half is true");

  struct S x;
  __CPROVER_assume(x.s == -3 && x.u == 30);
  float fs = x.s, fu = x.u;
  __CPROVER_assert(fs == -3.0f, "signed bit-field to float");
  __CPROVER_assert(fu == 30.0f, "unsigned bit-field to float");
  float g;
  __CPROVER_assume(g == -2.5f);
  x.s = g;
  __CPROVER_assert(x.s == -2, "float to signed bit-field");
  return 0;
}
