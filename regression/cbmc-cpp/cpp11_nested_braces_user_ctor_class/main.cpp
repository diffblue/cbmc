extern "C" void __CPROVER_assert(bool, const char *);
#include <string>
#include <utility>
struct F
{
  int v;
  template <class L>
  F(L l) : v(l())
  {
  }
  F(const F &) = default;
};
template <class T1, class T2>
struct P
{
  T1 first;
  T2 second;
  P(const T1 &a, const T2 &b) : first(a), second(b)
  {
  }
  template <class U1, class U2>
  P(U1 &&a, U2 &&b) : first(std::forward<U1>(a)), second(std::forward<U2>(b))
  {
  }
};
int main()
{
  // N5008 [dcl.init.list]/3.4: a class with a user-declared constructor is
  // initialised from a braced list by constructor overload resolution, not
  // memberwise.
  P<const char *, P<const char *, const F>> q{"a", {"b", []() { return 2; }}};
  __CPROVER_assert(
    q.second.second.v == 2,
    "nested braces into a class template with constructors");
  std::pair<const std::string, std::pair<const std::string, int>> r{
    "a", {"first", 1}};
  __CPROVER_assert(
    r.first == "a" && r.second.first == "first" && r.second.second == 1,
    "nested std::pair braces with strings");
  return 0;
}
