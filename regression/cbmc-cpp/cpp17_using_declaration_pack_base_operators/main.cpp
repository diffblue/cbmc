// N5008 [namespace.udecl]/1: a using-declarator may be a pack expansion,
// `using Bases::operator()...;' introducing every base's operator() into
// the derived class (the "overloaded" idiom; libc++ variant's
// __all_overloads).  Only the first base's operator() was introduced, so
// the overload set had one member and `all(1.0)' called A's int
// operator().
extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  int operator()(int) const
  {
    return 1;
  }
};
struct B
{
  int operator()(double) const
  {
    return 2;
  }
};
struct C
{
  int operator()(const char *) const
  {
    return 3;
  }
};
template <class... Bases>
struct All : Bases...
{
  using Bases::operator()...;
};
template <class F, class Arg>
using call_result_t =
  decltype(static_cast<const F &>(F{})(static_cast<Arg (*)()>(nullptr)()));
static_assert(__is_same(call_result_t<All<A, B>, double>, int), "overload set");
int main()
{
  All<A, B, C> all;
  __CPROVER_assert(all(1) == 1, "pack using: int");
  __CPROVER_assert(all(1.0) == 2, "pack using: double");
  __CPROVER_assert(all("x") == 3, "pack using: const char *");
  __CPROVER_assert(all(1.0) == 1, "WRONG (must FAIL)");
}
