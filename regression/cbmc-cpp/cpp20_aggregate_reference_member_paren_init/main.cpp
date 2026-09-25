// N5008 [dcl.init.general]/16.6.2.2 (C++20 parenthesized aggregate
// initialization) + [dcl.init.aggr]/4.2 + [dcl.init.ref]: an aggregate
// whose element is a REFERENCE is initializable with (...) as with {...},
// and the reference element is BOUND to its initializer.  CBMC treated
// the reference member as making the class non-POD and fell through to
// constructor resolution, which found only the synthesized copy
// constructor and dropped main.
extern "C" void __CPROVER_assert(bool, const char *);
struct ref_holder
{
  int &r_;
};
int main()
{
  int x = 7;
  ref_holder h{x};
  __CPROVER_assert(h.r_ == 7, "reference member braced init");
  ref_holder g(x);
  __CPROVER_assert(g.r_ == 7, "reference member paren init");
  return 0;
}
