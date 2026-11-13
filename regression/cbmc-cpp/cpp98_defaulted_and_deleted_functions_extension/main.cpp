extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [dcl.fct.def.default], [dcl.fct.def.delete] are C++11 features;
// g++ and clang++ accept them in C++98 mode as an extension
// (-Wc++11-extensions), and libc++ uses `= default' in every mode
struct S
{
  int k;
  S() : k(4)
  {
  }
  S(const S &) throw() = default;
  S &operator=(const S &) = delete;
};
int main()
{
  S a;
  S b(a);
  __CPROVER_assert(b.k == 4, "defaulted copy constructor");
  __CPROVER_assert(b.k == 0, "WRONG (must FAIL)");
  return 0;
}
