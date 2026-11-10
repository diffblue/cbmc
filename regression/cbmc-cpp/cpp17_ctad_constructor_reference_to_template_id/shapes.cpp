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
template <class T>
struct P1
{
  P1(const T &)
  {
  }
};
template <class T>
struct P2
{
  P2(T &)
  {
  }
};
template <class T>
struct P5
{
  P5(const W<T> *)
  {
  }
};
template <class T>
struct P6
{
  P6(const volatile W<T> &)
  {
  }
};
// [over.match.class.deduct]/1.1, [temp.deduct.call]/3: the guides formed
// from the constructors deduce from the type referred to by a reference
// parameter, without its cv-qualifiers
int main()
{
  int i = 1;
  const int ci = 2;
  W<char> w{'a'};
  P1 a(i);
  P1 a2(ci);
  P2 b(i);
  P2 b2(ci);
  P5 e(&w);
  P6 f(w);
  __CPROVER_assert(
    same<decltype(a), P1<int>>::value && same<decltype(a2), P1<int>>::value,
    "const T &");
  __CPROVER_assert(
    same<decltype(b), P2<int>>::value &&
      same<decltype(b2), P2<const int>>::value,
    "T &");
  __CPROVER_assert(same<decltype(e), P5<char>>::value, "const W<T> *");
  __CPROVER_assert(same<decltype(f), P6<char>>::value, "const volatile W<T> &");
  __CPROVER_assert(!same<decltype(f), P6<char>>::value, "WRONG (must FAIL)");
}
