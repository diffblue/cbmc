// N5008 [over.match.list]/1, [dcl.init.list]/3.7: `take({2, mk(E())})'
// with a by-value class parameter list-initializes it from the clauses
// (no initializer-list constructor: they are the constructor arguments).
// The clause `mk(E())' is type-checked once -- its forwarding-reference
// parameter binds the E prvalue as an xvalue ([temp.deduct.call]/3).  The
// front end type-checked the resolved call a second time while converting
// the list and bound the xvalue again, as an lvalue: "invalid implicit
// conversion from 'struct E &' to 'struct E &&'" (CBMC's own
// goto_clean_expr.cpp, `{1, std::make_pair(true_exprt(), replace_mapt())}'
// for a std::vector parameter, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct E
{
  int v = 7;
};
template <class A>
struct pr
{
  A a;
  pr(A x) : a(x)
  {
  }
};
template <class A>
pr<A> mk(A &&x)
{
  return pr<A>(x);
}
struct vec
{
  int n;
  vec(unsigned long count, const pr<E> &value) : n(count + value.a.v)
  {
  }
};
int take(vec b)
{
  return b.n;
}
int take_ref(const vec &b)
{
  return b.n * 10;
}
int main()
{
  __CPROVER_assert(take({2, mk(E())}) == 9, "by-value class parameter");
  __CPROVER_assert(take_ref({3, mk(E())}) == 100, "const reference parameter");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
