enum enm
{
  first = 1,
  second = 1 << 1,
  third = 1 << 2,
  fourth = 1 << 3,
};

static enum enm efunc(void)
{
  return second;
}

int main(void)
{
  enum enm e = efunc();
  __CPROVER_assert(__CPROVER_enum_is_in_range(e), "enum failure");
  return (e);
}
