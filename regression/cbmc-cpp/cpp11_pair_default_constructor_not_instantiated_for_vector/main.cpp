extern "C" void __CPROVER_assert(bool, const char *);
template <bool B, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  typedef T type;
};
template <class T>
struct is_default_constructible
{
  static constexpr bool value = __is_constructible(T);
};
// no default constructor
struct symbolish
{
  int x;
  symbolish(int v) : x(v)
  {
  }
};
template <class T1>
struct pair
{
  T1 first;
  // libstdc++'s constrained default constructor: not viable (and never
  // used) for a T1 without a default constructor
  template <
    class U1 = T1,
    typename enable_if<is_default_constructible<U1>::value, bool>::type = false>
  pair() : first()
  {
  }
  pair(const T1 &a) : first(a)
  {
  }
};
template <class T>
struct vector
{
  // libstdc++'s vector::_Temporary_value::_Storage shape: a member class
  // with a member of the element type; no object of it is created
  struct storage
  {
    T val;
  };
  int size = 0;
};
int main()
{
  vector<pair<symbolish>> v;
  pair<symbolish> p(symbolish(4));
  __CPROVER_assert(
    v.size == 0 && p.first.x == 4, "no default construction needed");
  __CPROVER_assert(p.first.x == 5, "WRONG (must FAIL)");
}
