extern "C" void __CPROVER_assert(bool, const char *);
enum token
{
  t_begin,
  t_end
};
struct pr
{
  char first;
  token second;
  pr(char c, token t) : first(c), second(t)
  {
  }
};
struct scanner
{
  int flags;
  explicit scanner(int f) : flags(f)
  {
  }
  // libstdc++'s _ScannerBase::_M_token_tbl: a const array of pairs with a
  // default member initializer made of nested braced lists
  const pr tbl[2] = {{'^', t_begin}, {'$', t_end}};
};
int main()
{
  scanner s(3);
  __CPROVER_assert(
    s.flags == 3 && s.tbl[1].first == '$' && s.tbl[1].second == t_end,
    "table initialized");
  __CPROVER_assert(s.tbl[0].first == '$', "WRONG (must FAIL)");
}
