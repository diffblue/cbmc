// N5008 [dcl.contract.res]/1, [basic.contract.eval]: a violated
// postcondition of a function returning a reference; the result name
// refers to the object the returned reference is bound to.
extern "C" void __CPROVER_assert(bool, const char *);
int a = 1, b = 2;
int &pick(const bool first) post(r : &r == &a)
{
  return first ? a : b;
}
int main()
{
  __CPROVER_assert(&pick(true) == &a, "a call satisfying the postcondition");
  // violates the postcondition: with the enforce semantic the program ends
  // here, so the postcondition is the property that must fail
  pick(false);
  return 0;
}
