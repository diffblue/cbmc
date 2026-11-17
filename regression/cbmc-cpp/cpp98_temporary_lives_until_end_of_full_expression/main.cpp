// N5008 [class.temporary]/4: temporary objects are destroyed as the last
// step in evaluating the full-expression that contains the point where they
// were created.  The temporary `make(42)' bound to view's constructor
// parameter lives until the end of the full-expression, so `use' may read
// it through the pointer view keeps (libstdc++'s
// std::vformat(fmt, std::make_format_args(x)) keeps a pointer into the
// _Arg_store temporary).
extern "C" void __CPROVER_assert(bool, const char *);

struct store
{
  int args[1];
};

store make(int x)
{
  store s;
  s.args[0] = x;
  return s;
}

struct view
{
  const int *p;
  view(const store &s) : p(s.args)
  {
  }
};

int use(view v)
{
  return v.p[0];
}

int main()
{
  __CPROVER_assert(use(make(42)) == 42, "temporary alive");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
