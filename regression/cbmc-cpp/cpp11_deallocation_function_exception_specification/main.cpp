// N5008 [except.spec]/9: a deallocation function with no explicit
// noexcept-specifier has a non-throwing exception specification, both a
// class member and a replacement at namespace scope.
#include <cstddef>
#include <cstdlib>
extern "C" void __CPROVER_assert(bool, const char *);

struct X
{
  static void operator delete(void *)
  {
  }
  static void operator delete[](void *)
  {
  }
  static void operator delete(void *, std::size_t) noexcept(false)
  {
  }
};

void operator delete(void *p) noexcept
{
  std::free(p);
}
void operator delete[](void *p)
{
  std::free(p);
}

int main()
{
  void *p = nullptr;
  __CPROVER_assert(noexcept(X::operator delete(p)), "member");
  __CPROVER_assert(noexcept(X::operator delete[](p)), "member, array");
  __CPROVER_assert(noexcept(::operator delete[](p)), "replacement, array");
  __CPROVER_assert(!noexcept(X::operator delete(p, 1)), "noexcept(false)");
  __CPROVER_assert(!noexcept(::operator delete(p)), "WRONG (must FAIL)");
  return 0;
}
