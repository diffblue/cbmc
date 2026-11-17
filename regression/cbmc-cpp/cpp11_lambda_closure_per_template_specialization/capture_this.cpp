// N5008 [expr.prim.lambda.closure]/1, [temp.spec.general]/1: as main.cpp,
// with a lambda capturing `this' in a virtual member function (the shape of
// libstdc++'s _Formatting_scanner::_M_format_arg)
extern "C" void __CPROVER_assert(bool, const char *);
struct scanner_base
{
  virtual int format_arg() = 0;
  int scan()
  {
    return format_arg();
  }
};
template <class C>
struct formatting_scanner : scanner_base
{
  C a = C(7);
  int format_arg() override
  {
    auto l = [this] { return int(sizeof(a)) + int(a); };
    return l();
  }
};
template <class C>
int do_format()
{
  formatting_scanner<C> s;
  return s.scan();
}
int main()
{
  int (*narrow)() = do_format<char>;
  __CPROVER_assert(do_format<long long>() == 15, "second specialization");
  __CPROVER_assert(narrow() == 8, "first specialization");
  __CPROVER_assert(narrow() == 15, "WRONG (must FAIL)");
}
