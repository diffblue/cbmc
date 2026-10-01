extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct W
{
  T v;
};
// [over.match.class.deduct]/1.1, [temp.deduct.call]/3: the guide formed from
// S(W<T> &) deduces T = int from an lvalue W<int>, as does that formed from
// R(const W<T> &, U) (libstdc++ 13's __format::_Formatting_scanner(
// basic_format_context<_Out, _CharT> &, basic_string_view<_CharT>))
template <class T>
struct S
{
  T x;
  S(W<T> &w) : x(w.v)
  {
  }
};
template <class T, class U>
struct R
{
  T x;
  R(const W<T> &w, U) : x(w.v)
  {
  }
};
int main()
{
  W<int> w{1};
  S s(w);
  __CPROVER_assert(s.x == 1, "reference");
  R r(w, 'c');
  __CPROVER_assert(r.x == 1, "const reference");
  __CPROVER_assert(s.x != 1, "WRONG (must FAIL)");
}
