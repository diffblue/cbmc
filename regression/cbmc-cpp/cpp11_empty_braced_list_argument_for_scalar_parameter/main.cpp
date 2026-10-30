// N5008 [over.ics.list]/10.2: for a parameter of non-class type, an empty
// initializer list is the identity conversion; the parameter is
// value-initialized ([dcl.init.list]/3.11), i.e. zero.  Overload
// resolution found no candidate for `h({})' with `int h(int)'.
extern "C" void __CPROVER_assert(bool, const char *);

enum class E
{
  a,
  b
};

int h(int i)
{
  return i;
}
double d(double x, int)
{
  return x;
}
bool p(const int *q)
{
  return q == nullptr;
}
bool e(E v)
{
  return v == E::a;
}
template <class T>
int one(int i, T)
{
  return i;
}
template <class... Vs>
int count(int, Vs...)
{
  return sizeof...(Vs);
}

int main()
{
  char c = 0;
  __CPROVER_assert(h({}) == 0, "int");
  __CPROVER_assert(d({}, 1) == 0.0, "double");
  __CPROVER_assert(p({}), "pointer");
  __CPROVER_assert(e({}), "scoped enumeration");
  __CPROVER_assert(one({}, c) == 0, "template");
  __CPROVER_assert(count({}, c) == 1, "variadic template");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
