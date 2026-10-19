extern "C" void __CPROVER_assert(bool, const char *);
namespace ns
{
struct sentinel
{
  // N5008 [class.friend]/7, [basic.lookup.argdep]/4.2: a friend function
  // first declared in a class is visible only to argument-dependent lookup
  // with that class associated
  template <class T>
  friend bool operator==(const T &, const T &)
  {
    return true;
  }
};
struct X
{
  int v;
};
} // namespace ns
template <class T>
constexpr bool has_eq = requires(const T &a, const T &b)
{
  a == b;
};
// a class template: the friend is declared by each specialization, and
// found for an argument whose associated classes include one ([basic.lookup.
// argdep]/3: a template argument's class)
template <class U>
struct box
{
  U u;
  friend int count(const box &)
  {
    return 1;
  }
  template <class V>
  friend int tag(const V &, const box &)
  {
    return 2;
  }
};
int main()
{
  __CPROVER_assert(!has_eq<ns::X>, "hidden friend not found for X");
  __CPROVER_assert(has_eq<ns::sentinel>, "found for sentinel");
  box<ns::X> b{};
  __CPROVER_assert(tag(0, b) == 2, "friend template found by ADL");
  __CPROVER_assert(has_eq<ns::X>, "WRONG (must FAIL)");
  return 0;
}
