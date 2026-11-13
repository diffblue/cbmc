// N5008 [stmt.contract.assert], [basic.contract.eval]: a violated assertion
// statement.
extern "C" void __CPROVER_assert(bool, const char *);
int half(int x)
{
  contract_assert(x % 2 == 0);
  return x / 2;
}
int main()
{
  __CPROVER_assert(half(4) == 2, "a call satisfying the assertion");
  // violates the assertion: with the enforce semantic the program ends here
  half(3);
  return 0;
}
