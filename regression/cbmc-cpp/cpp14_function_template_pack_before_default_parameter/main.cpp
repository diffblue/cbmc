extern "C" void __CPROVER_assert(bool, const char *);
struct P
{
  int v;
};
// [temp.param]/18: a function template's pack may be followed by a template
// parameter with a default argument (libc++'s `template <class... _Ts, bool
// _False = false> constexpr auto __get_comp_type()')
template <class... Ts, bool F = false>
constexpr int get()
{
  return sizeof...(Ts) + (F ? 100 : 0);
}
template <class... Ts, int N = 7>
constexpr int plus_n()
{
  return sizeof...(Ts) + N;
}
template <class... Ts>
struct wrap
{
  static constexpr int value = get<Ts...>();
};
static_assert(get<>() == 0, "empty");
static_assert(get<int, char>() == 2, "two explicit arguments, all to the pack");
static_assert(wrap<P, int, long>::value == 3, "forwarded pack");
static_assert(plus_n<P>() == 8, "non-type default after the pack");
int main()
{
  __CPROVER_assert(get<int, char, long>() == 3, "at run time");
  __CPROVER_assert(plus_n<>() == 7, "empty pack, default");
  __CPROVER_assert(get<int>() == 101, "WRONG (must FAIL)");
}
