// N5008 [dcl.spec.auto.general]/3: in a generic lambda's `const auto &x'
// only `auto' is replaced by the invented template parameter, so x is a
// reference to const and binds to an rvalue ([dcl.init.ref]/5.3)
extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  int v;
};
int main()
{
  int k = 1;
  auto f = [k](const auto &x) { return x + k; };
  auto g = [](const auto &x) { return x.v; };
  int four = 4;
  __CPROVER_assert(f(four) == 5, "lvalue");
  __CPROVER_assert(f(4) == 5, "rvalue");
  __CPROVER_assert(g(A{7}) == 7, "class rvalue");
  __CPROVER_assert(f(4) == 4, "WRONG (must FAIL)");
}
