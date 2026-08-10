extern "C" void __CPROVER_assert(bool, const char *);
struct it
{
  int v;
  int get() const
  {
    return v;
  }
};
struct pairt
{
  it first;
  bool second;
};
pairt make(int x)
{
  return pairt{it{x}, true};
}
int main()
{
  // [expr.ref]/8: member of a prvalue is an xvalue; [over.match.funcs]/5.3:
  // callable on rvalues for members without ref-qualifier.
  __CPROVER_assert(make(7).first.get() == 7, "member of call result callable");
  return 0;
}
