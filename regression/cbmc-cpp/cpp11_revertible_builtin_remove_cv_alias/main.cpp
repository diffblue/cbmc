// libstdc++ <= 12 declares alias templates named __remove_cv and
// __remove_reference (used as `__remove_cv<_Tp>'); GCC <= 12 and clang
// (which demotes the keyword on such a declaration, -Wkeyword-compat)
// accept this.  The scanner treats these names as builtins only when
// followed by '(', so the aliases stay identifiers.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct remove_cv
{
  typedef T type;
};
template <class T>
struct remove_cv<const T>
{
  typedef T type;
};
template <class T>
using __remove_cv = typename remove_cv<T>::type;
template <class T>
using __remove_reference = T;
template <class A, class B>
struct is_same
{
  static const bool value = false;
};
template <class A>
struct is_same<A, A>
{
  static const bool value = true;
};

int main()
{
  static_assert(is_same<__remove_cv<const int>, int>::value, "alias template");
  static_assert(is_same<__remove_reference<int>, int>::value, "alias");
  __remove_cv<const int> x = 3;
  __CPROVER_assert(x == 3, "alias type");
  return 0;
}
