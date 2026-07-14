// N5008 [unique.ptr.single.ctor]/1: the default constructor of
// std::unique_ptr value-initializes the stored pointer -- a default-
// constructed unique_ptr is null.  g++ and clang++ agree (runtime-checked).
//
// Fixed by modelling C++17 inheriting constructors ([namespace.udecl]/2,
// [class.inhctor.init]): libstdc++'s __uniq_ptr_data inherits its base's
// constructors via `using __uniq_ptr_impl::__uniq_ptr_impl;` and declares
// only defaulted move members, so its default construction goes through the
// inherited base default constructor -- which is exactly equivalent to a
// defaulted default constructor of the derived class, and is synthesized as
// such.  Previously the inherited default constructor was skipped, the
// member initializer `_M_t()` in unique_ptr's constructor found no candidate,
// the failure was swallowed for system headers, and the constructor became a
// silent no-op leaving the pointer nondet.

#include <memory>

extern "C" void __CPROVER_assert(int, const char *);

struct C
{
  int v;
  explicit C(int x) : v(x)
  {
  }
};

int main()
{
  std::unique_ptr<C> p;
  __CPROVER_assert(p.get() == nullptr, "default-constructed unique_ptr is null");
  return 0;
}
