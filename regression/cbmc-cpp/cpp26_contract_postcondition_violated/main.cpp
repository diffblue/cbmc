// N5008 [dcl.contract.func], [basic.contract.eval]: a postcondition violated
// on one return path only.
extern "C" void __CPROVER_assert(bool, const char *);
int clamp(const int x) post(r : r >= 0)
{
  if(x > 100)
    return 100;
  return x;
}
int main()
{
  __CPROVER_assert(clamp(500) == 100, "a call satisfying the postcondition");
  // violates the postcondition: with the enforce semantic the program ends
  // here, so the postcondition is the property that must fail
  clamp(-1);
  return 0;
}
