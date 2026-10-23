extern "C" void __CPROVER_assert(bool, const char *);
struct nat
{
};
struct ident
{
  template <class T>
  T &&operator()(T &&t) const
  {
    return static_cast<T &&>(t);
  }
};
template <class T>
T &&declval_();
// the fall back
template <class... Args>
nat invoke(Args &&...args);
// N5008 [temp.func.order], [temp.deduct.partial]/8, /11: with the same
// arguments this template is more specialized than invoke(Args&&...)
template <class F, class... Args>
decltype(declval_<F>()(declval_<Args>()...)) invoke(F &&f, Args &&...args)
{
  return static_cast<F &&>(f)(static_cast<Args &&>(args)...);
}
int main()
{
  ident id;
  const unsigned x = 7;
  __CPROVER_assert(invoke(id, x) == 7, "the more specialized template");
  __CPROVER_assert(invoke(id, x) == 8, "WRONG (must FAIL)");
  return 0;
}
