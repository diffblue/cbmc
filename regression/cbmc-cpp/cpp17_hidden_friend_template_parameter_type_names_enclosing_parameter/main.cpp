extern "C" void __CPROVER_assert(bool, const char *);
template <bool B, class T = void>
struct en
{
};
template <class T>
struct en<true, T>
{
  typedef T type;
};
template <class A, class B>
constexpr bool same_v = __is_same(A, B);
// N5008 [temp.local]/1, [class.friend]/7: in a friend function template
// defined in a class template, the enclosing template's parameters may be
// named in the friend's own template parameter list
template <class It>
struct rev
{
  It cur;
  template <class It2, typename en<same_v<It, It2>, int>::type = 0>
  friend int verify(const rev &, const rev<It2> &)
  {
    return 1;
  }
};
int main()
{
  rev<int *> a{nullptr}, b{nullptr};
  __CPROVER_assert(verify(a, b) == 1, "dependent parameter type");
  __CPROVER_assert(verify(a, b) == 2, "WRONG (must FAIL)");
  return 0;
}
