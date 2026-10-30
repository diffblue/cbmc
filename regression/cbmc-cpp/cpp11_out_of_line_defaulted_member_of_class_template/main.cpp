extern "C" void __CPROVER_assert(bool, const char *);
template <class C>
struct buf
{
  C *p;
  explicit buf(C *q) : p(q)
  {
  }
  buf(const buf &);
  buf &operator=(const buf &);
};
// [dcl.fct.def.default]/5: a special member function defaulted on its first
// declaration outside the class, libstdc++'s basic_streambuf
template <class C>
buf<C>::buf(const buf &) = default;
template <class C>
buf<C> &buf<C>::operator=(const buf &) = default;
int main()
{
  char c = 'x';
  buf<char> a(&c);
  buf<char> b(a);
  buf<char> d(nullptr);
  d = a;
  __CPROVER_assert(b.p == &c && d.p == &c, "defaulted copy");
  __CPROVER_assert(b.p == nullptr, "WRONG (must FAIL)");
}
