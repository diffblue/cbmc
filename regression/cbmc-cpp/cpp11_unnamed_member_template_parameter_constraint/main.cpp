// N5008 [temp.deduct.general]/5: a default template argument of a function
// template is substituted after deduction; an enable_if in it removes the
// candidate ([temp.deduct.general]/8).  An unnamed parameter of a member
// template must not be confused with the unnamed parameter of the enclosing
// class template (libstdc++'s _Optional_base: `bool = ...` in the class,
// `enable_if_t<..., bool> = false` in its constructors).
extern "C" void __CPROVER_assert(bool, const char *);
template <bool B, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  using type = T;
};
template <bool B, class T = void>
using enable_if_t = typename enable_if<B, T>::type;

template <class T, bool = sizeof(T) == 4>
struct base
{
  int v = 0;
  template <class U, enable_if_t<sizeof(U) == 8, bool> = false>
  base(U &&) : v(8)
  {
  }
  template <class U, enable_if_t<sizeof(U) != 8, bool> = false>
  base(U &&) : v(1)
  {
  }
};
struct S
{
  int x, y;
};
int main()
{
  base<S> a(S{1, 2});
  base<S> b('c');
  __CPROVER_assert(a.v == 8, "enabled constructor for an 8-byte argument");
  __CPROVER_assert(b.v == 1, "enabled constructor for a 1-byte argument");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
