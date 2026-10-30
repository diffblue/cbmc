extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_type;
// libc++ <string>'s basic_string::__recommend shape: a template-id whose
// non-type argument is a conditional expression containing an unparenthesized
// `<' ([temp.names]/3: the first non-nested `>' ends the argument list; `<'
// inside an argument is an operator)
template <class CharT>
struct basic_string
{
  using value_type = CharT;
  enum
  {
    __min_cap = 23 / sizeof(value_type) < 2 ? 2 : 23 / sizeof(value_type)
  };
  template <size_type __a>
  static constexpr size_type __align_it(size_type __s) noexcept
  {
    return (__s + (__a - 1)) & ~(__a - 1);
  }
  enum
  {
    __alignment = 8
  };
  static constexpr size_type __recommend(size_type __s) noexcept
  {
    if(__s < __min_cap)
      return static_cast<size_type>(__min_cap) - 1;
    size_type __guess = __align_it < sizeof(value_type) < __alignment
                          ? __alignment / sizeof(value_type)
                          : 1 > (__s + 1) - 1;
    if(__guess == __min_cap)
      ++__guess;
    return __guess;
  }
};
template <unsigned A>
constexpr unsigned align_it(unsigned s)
{
  return (s + (A - 1)) & ~(A - 1);
}
unsigned g(unsigned s)
{
  return align_it < 1 < 8 ? 8 : 1 > (s + 1) - 1;
}
int main()
{
  __CPROVER_assert(basic_string<char>::__recommend(5) == 22, "below min cap");
  __CPROVER_assert(
    basic_string<char>::__recommend(30) == 31, "aligned up (char)");
  __CPROVER_assert(
    basic_string<int>::__recommend(30) == 31, "aligned up (int)");
  __CPROVER_assert(
    basic_string<char>::__recommend(23) == 24, "guess equals min cap");
  __CPROVER_assert(g(30) == 31, "non-member template-id in a return statement");
  __CPROVER_assert(g(30) == 30, "WRONG (must FAIL)");
}
