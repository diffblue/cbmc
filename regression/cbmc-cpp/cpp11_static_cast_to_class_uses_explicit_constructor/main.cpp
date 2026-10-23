extern "C" void __CPROVER_assert(bool, const char *);
template <class It>
struct reversed
{
  It cur;
  constexpr explicit reversed(It i) : cur(i)
  {
  }
};
// N5008 [expr.static.cast]/4, [over.match.ctor]/1: `static_cast<T>(e)' is
// the direct-initialization `T t(e);', which may use an explicit
// constructor (the MSVC STL's reverse_iterator::_Unwrapped)
int main()
{
  int a[2] = {1, 2};
  reversed<int *> r = static_cast<reversed<int *>>(a + 1);
  __CPROVER_assert(*r.cur == 2, "explicit constructor used");
  __CPROVER_assert(*r.cur == 1, "WRONG (must FAIL)");
  return 0;
}
