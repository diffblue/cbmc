extern "C" void __CPROVER_assert(bool, const char *);

// [over.match.funcs.general]/5: no user-defined conversion binds the
// implicit object parameter; for a const object only the const conversion
// function is viable (Google Benchmark's Counter)
struct counter
{
  double value;
  double other;
  operator double() const
  {
    return value;
  }
  operator double &()
  {
    return other;
  }
  const counter at() const
  {
    return *this;
  }
};

int main()
{
  counter c;
  c.value = 3.0;
  c.other = 5.0;
  const counter &cc = c;
  __CPROVER_assert(long(c.at()) == 3, "const rvalue");
  __CPROVER_assert(long(cc) == 3, "const lvalue");
  __CPROVER_assert(long(c) == 5, "non-const lvalue");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
