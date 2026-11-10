// Without an explicit --cpp<NN>, the dialect is the host compiler's default
// (g++/clang++ without -std=: gnu++17 for g++ 11 and later, gnu++14 for
// g++ 6 to 10), as goto-cc's gcc mode already did; the built-in default
// used to be C++98, in which `static_assert', `nullptr', `constexpr' and
// `auto' are not keywords -- they were accepted only through uninitialized
// parser flags.  Every supported host compiler defaults to at least C++14.
extern "C" void __CPROVER_assert(bool, const char *);
static_assert(__cplusplus >= 201402L, "at least C++14 by default");
constexpr int square(int x)
{
  return x * x;
}
int main()
{
  auto p = nullptr;
  int *q = p;
  static_assert(square(3) == 9, "constexpr");
  __CPROVER_assert(q == nullptr, "nullptr");
  return 0;
}
