// N5008 [class.temporary], [dcl.init.general]: returning a prvalue of a type
// whose copy constructor is deleted.
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  S() = default;
  S(const S &) = delete;
  int v = 4;
};
S f()
{
  return S{};
}
int main()
{
  S s = f();
  __CPROVER_assert(s.v == 4, "no copy of a prvalue");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
