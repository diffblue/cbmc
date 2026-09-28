extern "C" void __CPROVER_assert(bool, const char *);
// [temp.param]/18: a function template's pack may be followed by a
// defaulted template parameter; [temp.arg.explicit]/9: template argument
// deduction can extend a pack beyond its explicitly specified arguments
template <class... Ts, int N = 7>
int sum(Ts... xs)
{
  return (0 + ... + xs) + N;
}
template <class... Ts>
int count(Ts...)
{
  return sizeof...(Ts);
}
int main()
{
  __CPROVER_assert(count<int>(1, 2, 3) == 3, "pack extended by deduction");
  __CPROVER_assert(sum<int>(1, 2) == 10, "extended pack followed by a default");
  __CPROVER_assert(sum(1, 2) == 10, "fully deduced");
  __CPROVER_assert(sum<int>(1, 2) == 11, "WRONG (must FAIL)");
}
