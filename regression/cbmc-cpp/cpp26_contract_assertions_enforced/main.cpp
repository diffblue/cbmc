// N5008 [basic.contract.eval], [dcl.contract.func], [stmt.contract.assert]:
// with the enforce evaluation semantic every contract assertion is checked:
// preconditions before the body, postconditions at each return (also of a
// void function, and when its end is reached), assertion statements where
// they are.  All of them hold here.
extern "C" void __CPROVER_assert(bool, const char *);
int sign(const int x) pre(x != 0) post(r : r == 1 || r == -1)
{
  if(x > 0)
    return 1;
  return -1;
}
int count = 0;
void bump(const int by) pre(by > 0) post(count >= by)
{
  count += by;
}
struct Acc
{
  int total = 0;
  void add(const int v) pre(v >= 0) post(total >= v)
  {
    total += v;
  }
};
int sum(const int n) pre(n >= 0)
{
  int s = 0;
  for(int i = 0; i < n; ++i)
  {
    contract_assert(s == i * (i - 1) / 2);
    s += i;
  }
  return s;
}
int main()
{
  Acc a;
  a.add(3);
  bump(2);
  __CPROVER_assert(
    sign(5) == 1 && sign(-2) == -1 && count == 2 && a.total == 3 && sum(4) == 6,
    "contracts hold");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
