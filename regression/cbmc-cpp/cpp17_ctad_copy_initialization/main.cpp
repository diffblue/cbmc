extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct sp
{
  T v;
  sp(T q) : v(q)
  {
  }
};
sp<int> make()
{
  return sp<int>(4);
}
// [dcl.type.class.deduct]/1, [over.match.class.deduct]/5: for `sp s = e;'
// the initializer of class template argument deduction is e; the copy
// deduction candidate deduces sp<int> from an sp<int> (libstdc++'s
// _Sink::_M_write: `span __to = _M_unused();')
int main()
{
  sp<int> a(1);
  sp b = a;
  sp c = make();
  sp d = 7;
  __CPROVER_assert(b.v == 1, "from an lvalue");
  __CPROVER_assert(c.v == 4, "from a call");
  __CPROVER_assert(d.v == 7, "from a constructor argument");
  __CPROVER_assert(c.v != 4, "WRONG (must FAIL)");
}
