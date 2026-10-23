extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
concept small = sizeof(T) <= 64;
namespace pipe
{
struct third
{
  int operator()(int (&a)[5]) const
  {
    return a[2];
  }
};
// N5008 [basic.scope.param]/1, [dcl.decl.general]/4: the trailing
// requires-clause names the function parameters l and r (the MSVC STL's
// range adaptor closure operator|)
template <class L, class R>
requires(small<R>) constexpr decltype(auto)
operator|(L &&l, R &&r) requires requires
{
  static_cast<R &&>(r)(static_cast<L &&>(l));
}
{
  return static_cast<R &&>(r)(static_cast<L &&>(l));
}
} // namespace pipe
int main()
{
  int a[5] = {1, 2, 3, 4, 5};
  pipe::third c;
  __CPROVER_assert((a | c) == 3, "pipe through the closure");
  __CPROVER_assert((a | c) == 2, "WRONG (must FAIL)");
  return 0;
}
