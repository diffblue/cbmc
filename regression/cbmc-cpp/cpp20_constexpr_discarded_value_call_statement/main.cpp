// N5008 [stmt.expr]/1: the expression of an expression statement is a
// discarded-value expression ([expr.context]/2); it is evaluated.  A call
// in such a statement may appear in a constexpr function evaluated within a
// constant expression ([expr.const]/10 does not exclude it): here a
// precondition check whose result is ignored, as a library may write it.
extern "C" void __CPROVER_assert(bool, const char *);

constexpr bool check(unsigned long i) noexcept
{
  return i < 4;
}

struct view
{
  const char *str;
  constexpr char operator[](unsigned long i) const
  {
    check(i);
    return str[i];
  }
};

consteval view letters()
{
  return {"\tab"};
}

bool is_tab(char c)
{
  switch(c)
  {
  case letters()[0]:
    return true;
  default:
    return false;
  }
}

int main()
{
  constexpr char second = letters()[1];
  __CPROVER_assert(second == 'a', "constant initializer");
  __CPROVER_assert(is_tab('\t'), "case label");
  __CPROVER_assert(!is_tab('a'), "default");
  __CPROVER_assert(is_tab('a'), "WRONG (must FAIL)");
  return 0;
}
