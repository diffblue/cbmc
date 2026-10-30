// C++11 explicit conversion operator
struct Bool
{
  bool val;
  Bool(bool v) : val(v)
  {
  }
  explicit operator bool() const
  {
    return val;
  }
};
int main()
{
  Bool b(true);
  if(b)
  {
    __CPROVER_assert(true, "explicit bool conversion");
  }
  else
  {
    __CPROVER_assert(false, "should not reach");
  }
  return 0;
}
