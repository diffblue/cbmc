// N5008 [temp.variadic]/5, [dcl.fct]/2: `-> decltype(g(I...))' in a member
// of a class template with the non-type pack I expands to one argument per
// element of I.  The member's type was checked with only I's first element
// bound to its name, so g was called with one argument and the member's
// declaration failed.  libc++'s __perfect_forward_impl<_Op,
// index_sequence<_Idx...>, ...>::operator() is declared this way (reduced
// from std::invoke_result_t of a std::__bind_back closure).
extern "C" void __CPROVER_assert(bool, const char *);
int g(unsigned long, unsigned long)
{
  return 1;
}
template <unsigned long... I>
struct prim
{
  auto f() -> decltype(g(I...));
  auto h() -> decltype(g(I...))
  {
    return g(I...);
  }
};
template <class>
struct spec;
template <unsigned long...>
struct seq
{
};
template <class Op, class Idx>
struct spec2;
template <class Op, unsigned long... I>
struct spec2<Op, seq<I...>>
{
  auto operator()() -> decltype(Op()(I...));
};
template <unsigned long... I>
struct spec<seq<I...>>
{
  auto h() -> decltype(g(I...))
  {
    return g(I...);
  }
};
template <class F>
decltype(F()()) call(F);
struct op
{
  template <class A, class B>
  auto operator()(A, B) -> decltype(0);
};
struct bound : spec2<op, seq<0, 1>>
{
};

int main()
{
  __CPROVER_assert(
    __is_same(decltype(prim<0, 1>().f()), int), "primary, declared");
  __CPROVER_assert(prim<0, 1>().h() == 1, "primary, defined");
  __CPROVER_assert(spec<seq<0, 1>>().h() == 1, "partial specialization");
  __CPROVER_assert(
    __is_same(decltype(call(bound())), int), "invoked through a base");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
