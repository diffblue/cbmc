extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [temp.param]/17, [temp.arg.explicit]/4: `int &...' is a template
// parameter pack of non-type parameters; a trailing pack not otherwise
// deduced is deduced as empty, so `f()' and `f<>()' call the specialization
// with no template arguments (libc++'s pair::_CheckArgs)
struct checks
{
  template <int &...>
  static constexpr bool implicit_default()
  {
    return true;
  }
  template <int &...>
  static constexpr bool explicit_default()
  {
    return !implicit_default<>();
  }
};
int a, b;
template <int *...P>
constexpr int count()
{
  return sizeof...(P);
}
template <bool B>
struct w
{
  static const int value = B;
};
int main()
{
  __CPROVER_assert(w<checks::implicit_default()>::value == 1, "f()");
  __CPROVER_assert(w<checks::explicit_default<>()>::value == 0, "f<>()");
  __CPROVER_assert(checks::implicit_default(), "call");
  __CPROVER_assert(count<&a, &b>() == 2, "non-empty pointer pack");
  __CPROVER_assert(!checks::implicit_default(), "WRONG (must FAIL)");
  return 0;
}
