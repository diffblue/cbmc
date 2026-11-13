// N5008 [stmt.contract.assert], [basic.contract.eval]: a call satisfying the
// contract.
extern "C" void __CPROVER_assert(bool, const char *);
int f(const int x) pre(x > 0) post(r : r == x + 1)
{
  contract_assert(x != 3);
  return x + 1;
}
int main()
{
  __CPROVER_assert(f(1) == 2, "a call satisfying the contract");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
