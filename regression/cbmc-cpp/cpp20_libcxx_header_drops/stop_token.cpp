#include <stop_token>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  // libc++ 18 declares std::stop_source only with -fexperimental-library;
  // the header's inline functions are type-checked regardless
  __CPROVER_assert(true, "header");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
