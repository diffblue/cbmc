extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int k;
  // N5008 [temp.deduct.call]/3, [dcl.fct]/6: for a const object, Self
  // deduces as const S &
  template <class Self>
  int get(this Self &&self)
  {
    return self.k;
  }
};
int main()
{
  const S c{3};
  S m{4};
  __CPROVER_assert(c.get() == 3 && m.get() == 4, "const and non-const object");
  __CPROVER_assert(c.get() == 4, "WRONG (must FAIL)");
  return 0;
}
