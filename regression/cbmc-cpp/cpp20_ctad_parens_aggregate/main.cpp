// N5008 [dcl.init.general]/16.6.2.2 (C++20): T(a1, ..., an) with T an
// aggregate and no viable constructor performs aggregate
// initialization, as the braced form does; combined with CTAD
// ([over.match.class.deduct]) this is libc++'s make_pair spelling
// `return pair(t1, t2)`.  CBMC used to reject the POD case with
// "explicit typecast expects 0 or 1 operands" and silently no-body the
// enclosing template instance (fifth layer of the vector push_back
// family).
extern "C" void __CPROVER_assert(bool, const char *);

template <class A, class B>
struct pair
{
  A first;
  B second;
};

template <class A, class B>
pair<A, B> make_pair(A a, B b)
{
  return pair(a, b);
}

int main()
{
  auto p = make_pair(1, 2);
  __CPROVER_assert(p.first == 1 && p.second == 2, "ctad parens");
}
