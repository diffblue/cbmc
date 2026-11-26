extern "C" void __CPROVER_assert(bool, const char *);
template <class A, class B>
struct same
{
  static const bool value = false;
};
template <class A>
struct same<A, A>
{
  static const bool value = true;
};
template <class T>
struct W
{
  T v;
};
// [over.match.class.deduct]/1.1, [temp.deduct.call]/3: the guide formed from
// P(W<T> &&) deduces T = short from the prvalue W<short>{3}
template <class T>
struct P
{
  T x;
  P(W<T> &&w) : x(w.v)
  {
  }
};
int main()
{
  P d(W<short>{3});
  __CPROVER_assert(same<decltype(d), P<short>>::value && d.x == 3, "rvalue");
  __CPROVER_assert(d.x != 3, "WRONG (must FAIL)");
}
