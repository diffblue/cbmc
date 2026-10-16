extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
concept has_begin = requires(T &t) { t.begin(); };
struct fn
{
  template <class T>
    requires has_begin<T>
  int operator()(T &&t) const
  {
    return t.begin();
  }
  // N5008 [temp.func.order]/6.4: both templates are equally specialized;
  // the constrained one is more specialized and the deleted one loses
  template <class U>
  void operator()(U &&) const = delete;
};
struct R
{
  int begin()
  {
    return 7;
  }
};
int main()
{
  R r;
  int b = fn{}(r);
  __CPROVER_assert(b == 7, "constrained overload");
  __CPROVER_assert(b == 0, "WRONG (must FAIL)");
  return 0;
}
