// N5008 [temp.pre]: a variable template.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
constexpr T pi = T(3);
int main()
{
  __CPROVER_assert(pi<int> == 3, "variable template");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
