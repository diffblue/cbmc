extern "C" void __CPROVER_assert(bool, const char *);
// a union with a user-provided constructor (and destructor), returned by
// value from a named object, a global and a parameter
union value
{
  value() : i(0)
  {
  }
  ~value()
  {
  }
  int i;
  float f;
};
value global;
value from_global()
{
  return global;
}
value from_local(int x)
{
  value v;
  v.i = x;
  return v;
}
value from_parameter(value p)
{
  return p;
}
int main()
{
  global.i = 3;
  __CPROVER_assert(from_global().i == 3, "global");
  __CPROVER_assert(from_local(4).i == 4, "local");
  value p;
  p.i = 5;
  __CPROVER_assert(from_parameter(p).i == 5, "parameter");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
