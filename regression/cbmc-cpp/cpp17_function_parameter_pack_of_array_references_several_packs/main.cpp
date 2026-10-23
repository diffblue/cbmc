// N5008 [temp.variadic]/5, /7: with several template packs, the function
// parameter pack `const char (&...s)[N]' belongs to the NON-type pack N.
// For an empty N it has no parameters, and for a non-empty one it has one
// per element (cpp17_function_parameter_pack_of_array_references); with
// several packs the pack was looked for among the TYPE packs only.
extern "C" void __CPROVER_assert(bool, const char *);
template <class... T>
struct tl
{
};
constexpr int count()
{
  return 0;
}
template <class... S>
constexpr int count(const char *, S... s)
{
  return 1 + count(s...);
}
struct base
{
  template <class... T, unsigned long... N>
  static int h(tl<T...>, const char (&...s)[N])
  {
    return (int)sizeof...(T) * 10 + count(s...);
  }
};
template <class... T, unsigned long... N>
int g(tl<T...>, const char (&...s)[N])
{
  return (int)sizeof...(T) * 10 + count(s...);
}
int main()
{
  __CPROVER_assert(g(tl<int>{}) == 10, "free, empty");
  __CPROVER_assert(g(tl<int>{}, "ab", "c") == 12, "free, two");
  __CPROVER_assert(base::h(tl<int, char>{}) == 20, "member, empty");
  __CPROVER_assert(base::h(tl<int>{}, "ab") == 11, "member, one");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
