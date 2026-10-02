extern "C" void __CPROVER_assert(bool, const char *);
// [over.match.class.deduct]/1.1, [temp.deduct.call]/3: CTAD from a call
// result, an xvalue, a functional cast and a braced list
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
template <class T>
struct P
{
  T x;
  P(W<T> &&w) : x(w.v)
  {
  }
};
template <class T>
struct Q
{
  T x;
  Q(T t) : x(t)
  {
  }
};
W<long> make()
{
  return W<long>{7};
}
int main()
{
  P a(make());
  W<char> w{'c'};
  P b(static_cast<W<char> &&>(w));
  Q c(W<int>{2});
  Q d{W<int>{2}};
  __CPROVER_assert(
    same<decltype(a), P<long>>::value && a.x == 7, "call result");
  __CPROVER_assert(same<decltype(b), P<char>>::value && b.x == 'c', "xvalue");
  __CPROVER_assert(
    same<decltype(c), Q<W<int>>>::value && c.x.v == 2,
    "functional cast by value");
  __CPROVER_assert(same<decltype(d), Q<W<int>>>::value, "braced");
  __CPROVER_assert(a.x != 7, "WRONG (must FAIL)");
}
