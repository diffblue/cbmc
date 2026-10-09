// N5008 [temp.spec.partial.match], [temp.variadic]/5, [expr.prim.fold]: a
// partial specialization may have several packs; a fold over any of them,
// in a member's body or trailing return type, expands over the elements
// matching deduced.  Only the last pack was expanded, and `(I + ...)'
// over the first one was left to a placeholder.  libc++'s
// __perfect_forward_impl<_Op, index_sequence<_Idx...>, _BoundArgs...> does
// this.
extern "C" void __CPROVER_assert(bool, const char *);
template <int...>
struct seq
{
};
template <class, class...>
struct S;
template <int... I, class... B>
struct S<seq<I...>, B...>
{
  int sum()
  {
    return (I + ...);
  }
  int count()
  {
    return sizeof...(B);
  }
  int index_count()
  {
    return sizeof...(I);
  }
  template <class... A>
  auto f(A...) -> decltype((I + ...))
  {
    return (I + ...) + 10;
  }
};
int main()
{
  S<seq<1, 2>, char, long> s;
  __CPROVER_assert(s.sum() == 3, "sum of I");
  __CPROVER_assert(s.count() == 2, "sizeof B");
  __CPROVER_assert(s.index_count() == 2, "sizeof I");
  S<seq<4, 5>, char> t;
  __CPROVER_assert(t.sum() == 9 && t.count() == 1, "one B");
  __CPROVER_assert(s.f() == 13, "trailing return type");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
