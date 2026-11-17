// N5008 [dcl.inline]: an inline static data member.
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  static inline int n = 4;
};
int main()
{
  __CPROVER_assert(S::n == 4, "inline static data member");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
