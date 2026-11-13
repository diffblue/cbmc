// N5008 [dcl.contract.res]/1, [basic.contract.eval]: a violated
// postcondition of a function returning a class (by guaranteed copy
// elision, the result object is the caller's).
extern "C" void __CPROVER_assert(bool, const char *);
struct T
{
  int v;
  T(int x) : v(x)
  {
  }
  ~T()
  {
  }
};
T make(const int x) post(r : r.v == x)
{
  return T{x == 3 ? 4 : x};
}
int main()
{
  __CPROVER_assert(make(1).v == 1, "a call satisfying the postcondition");
  // violates the postcondition: with the enforce semantic the program ends
  // here, so the postcondition is the property that must fail
  make(3);
  return 0;
}
