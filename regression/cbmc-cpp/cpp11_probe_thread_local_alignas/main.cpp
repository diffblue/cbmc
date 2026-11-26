// N5008 [dcl.stc], [dcl.align]: alignas and thread_local.
extern "C" void __CPROVER_assert(bool, const char *);
struct alignas(16) S
{
  char c;
};
thread_local int t = 3;
int main()
{
  __CPROVER_assert(alignof(S) == 16 && t == 3, "alignas and thread_local");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
