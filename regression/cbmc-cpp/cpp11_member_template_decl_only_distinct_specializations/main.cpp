extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
T &&declval() noexcept;
template <class T>
struct success
{
  typedef T type;
  static constexpr int n = sizeof(T);
};
struct A
{
  template <class Fn, class... Args>
  static success<decltype(declval<Fn>()(declval<Args>()...))> t1(int);
};
struct B
{
  template <class Fn, class Arg>
  static success<decltype(declval<Fn>()(declval<Arg>()))> t2(int);
};
struct C
{
  template <class Fn, class... Args>
  static success<Fn> t3(int);
};
using LFP = long (*)(int);
using FP2 = int (*)(int, int);
int main()
{
  __CPROVER_assert(
    decltype(A::t1<LFP &, int &>(0))::n == sizeof(long), "A first");
  __CPROVER_assert(
    decltype(A::t1<FP2 &, int &, int &>(0))::n == sizeof(int),
    "A second (pack + decltype)");
  __CPROVER_assert(
    decltype(B::t2<LFP &, int &>(0))::n == sizeof(long), "B first");
  __CPROVER_assert(
    decltype(B::t2<int (*&)(int), int &>(0))::n == sizeof(int),
    "B second (no pack, decltype)");
  __CPROVER_assert(decltype(C::t3<long, int>(0))::n == sizeof(long), "C first");
  __CPROVER_assert(
    decltype(C::t3<int, int, int>(0))::n == sizeof(int),
    "C second (pack, no decltype)");
  return 0;
}
