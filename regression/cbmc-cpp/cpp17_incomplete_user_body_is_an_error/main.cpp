// User-reported Issue 13 (second half, soundness).  A user function whose
// body the front-end cannot fully type-check used to be kept incomplete with
// a warning, and the run reported VERIFICATION SUCCESSFUL with exit 0 and no
// properties.  This program is ill-formed (the only conversion function's
// constraint is false for `unsigned long'; g++ rejects it), so the front-end
// must reject it too: CONVERSION ERROR, exit 6, no SUCCESSFUL verdict.
extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>
template <class T>
struct Wrap
{
  T v;
  template <class U, class = std::enable_if_t<std::is_same_v<U, char>>>
  operator U() const
  {
    return static_cast<U>(v);
  }
};
int main()
{
  Wrap<unsigned> w{5};
  unsigned long h = w;
  __CPROVER_assert(h == 5, "never reached");
  return 0;
}
