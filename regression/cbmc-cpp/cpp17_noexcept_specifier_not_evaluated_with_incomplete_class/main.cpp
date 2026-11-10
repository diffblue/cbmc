// N5008 [except.spec]/12, [temp.inst]/3: the noexcept-specifier of a member
// of a class template specialization is instantiated when it is needed,
// not with the class.  Instantiating it with the class evaluated
// `nothrow_move<leaf>' while leaf<int> was still incomplete, and the false
// result stuck: libc++'s __tuple_leaf<0, int &&> (Xcode 26), whose swap is
// `noexcept(__is_nothrow_swappable_v<__tuple_leaf>)', was not nothrow move
// constructible, and std::forward_as_tuple lost its body.
extern "C" void __CPROVER_assert(bool, const char *);

template <class U>
inline const bool nothrow_move = __is_nothrow_constructible(U, U &&);

template <class H>
struct leaf
{
  H value;
  template <class T>
  leaf(T &&t, int) noexcept(false) : value(t)
  {
  }
  leaf(leaf &&) = default;
  int swap(leaf &) noexcept(nothrow_move<leaf>)
  {
    return 0;
  }
};

template <class T>
struct W
{
  static void f() noexcept(sizeof(T) == 1)
  {
  }
};

int main()
{
  static_assert(nothrow_move<leaf<int>>, "nothrow move constructible");
  leaf<int> a(1, 0), b(2, 0);
  static_assert(noexcept(a.swap(b)), "swap is noexcept");
  // [except.spec]/12.1: needed when f is selected for its type
  void (*nothrow)() noexcept = &W<char>::f;
  void (*any)() = &W<int>::f;
  __CPROVER_assert(nothrow != nullptr && any != nullptr, "addresses");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
