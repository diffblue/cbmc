// C++17 if with init-statement and structured bindings
struct Result
{
  bool ok;
  int val;
};

Result get()
{
  Result r;
  r.ok = true;
  r.val = 42;
  return r;
}

int main()
{
  if(auto [ok, val] = get(); ok)
  {
    __CPROVER_assert(val == 42, "if init sb");
  }
  return 0;
}
