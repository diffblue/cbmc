extern "C" void __CPROVER_assert(bool, const char *);
template <typename, typename>
struct replace_first;
// N5008 [temp.arg.template]/1, [temp.res.general]: Tmpl names the class
// template the argument denotes, wherever that is declared
template <template <typename...> class Tmpl, typename U, typename T>
struct replace_first<Tmpl<T>, U>
{
  using type = Tmpl<U>;
};
namespace ns
{
template <typename T>
struct box
{
  T v;
};
} // namespace ns
int main()
{
  replace_first<ns::box<int>, char>::type b{'x'};
  __CPROVER_assert(sizeof(b) == 1 && b.v == 'x', "box<char>");
  __CPROVER_assert(b.v == 'y', "WRONG (must FAIL)");
  return 0;
}
