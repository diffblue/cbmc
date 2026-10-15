// N5008 [over.over]/1: the name of an overload set used to initialize a
// pointer to function (/1.1) or as the operand of an explicit type
// conversion (/1.3) selects the function whose type matches the target.
// The front end only did this for call arguments: `int (*g)(int) = pick'
// and `static_cast<const ex &(*)(const ex &)>(pick)' did "not uniquely
// resolve" (CBMC's own statement_list_parser.cpp, a cast of the overloaded
// to_symbol_expr passed to std::transform, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct ex
{
  int v = 3;
};
const ex &pick(const ex &e)
{
  return e;
}
ex &pick(ex &e)
{
  return e;
}
int twice(int x)
{
  return 2 * x;
}
long twice(long x)
{
  return 3 * x;
}
int main()
{
  auto f = static_cast<const ex &(*)(const ex &)>(pick);
  const ex &(*g)(const ex &) = pick;
  long (*h)(long) = &twice;
  ex e;
  __CPROVER_assert(f(e).v == 3 && g(e).v == 3, "reference overloads");
  __CPROVER_assert(h(2) == 6, "value overloads");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
