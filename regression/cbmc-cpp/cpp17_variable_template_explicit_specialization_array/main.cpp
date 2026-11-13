extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [temp.expl.spec]/1, /7: an explicit specialization of a variable
// template, declared before its first use, is the entity the use names.
// [basic.link]/11: its array type may add the bound the primary template's
// declaration leaves out (the MSVC STL's __DIGIT_TABLE), and declared at
// namespace scope it has static storage duration ([basic.stc.static]/1)
template <class C>
constexpr C table[] = {C{}};
template <>
inline constexpr char table<char>[4] = {'0', '1', '2', '3'};
template <class C>
constexpr int pair[2] = {1, 1};
template <>
constexpr int pair<char>[2] = {2, 3};
const int *const p = pair<char>;
int main()
{
  __CPROVER_assert(table<char>[2] == '2', "specialization");
  __CPROVER_assert(sizeof(table<char>) == 4, "its bound");
  __CPROVER_assert(table<int>[0] == 0, "primary");
  __CPROVER_assert(p[1] == 3, "static storage duration");
  __CPROVER_assert(table<char>[1] == '0', "WRONG (must FAIL)");
  return 0;
}
