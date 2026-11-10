// N5008 [expr.prim.id.dtor]/1, [class.dtor]/16: in `f.~F()' with the
// template parameter F naming a class, ~F names that class's destructor.
// libc++'s std::function destroys a std::bind result `__bind<int (&)(int,
// int), const placeholders::__ph<1> &, int>' this way (`__func_.~_Fp()').
extern "C" void __CPROVER_assert(bool, const char *);
#include <new>

int destroyed = 0;

namespace n
{
template <int N>
struct ph
{
};
} // namespace n

template <class Fn, class... Args>
struct bound
{
  int v = 1;
  ~bound()
  {
    ++destroyed;
  }
};

template <class F>
struct holder
{
  F f;
  void destroy() noexcept
  {
    f.~F();
  }
};

int add(int a, int b)
{
  return a + b;
}

int main()
{
  holder<bound<int (&)(int, int), const n::ph<1> &, int>> h;
  h.destroy();
  __CPROVER_assert(destroyed == 1, "destructor called");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  // h.f is destroyed again at the end of main; the test does not rely on it
  new(&h.f) bound<int (&)(int, int), const n::ph<1> &, int>;
  return 0;
}
