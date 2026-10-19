extern "C" void __CPROVER_assert(bool, const char *);
template <class... Ts>
struct L
{
};
template <class, class>
struct find;
// N5008 [temp.variadic]/5, [temp.spec.partial.match]/2: in a partial
// specialization, a pack expansion over a deduced pack R expands to one
// element per deduced argument (the MSVC STL's _Meta_find_unique_index_)
template <class F, class... R, class T>
struct find<L<F, R...>, T>
{
  static constexpr int sizes[3] = {sizeof(F), sizeof(R)...};
  static constexpr bool same[2] = {__is_same(R, T)...};
};
int main()
{
  using X = find<L<int, char, long>, long>;
  __CPROVER_assert(
    X::sizes[1] == 1 && X::sizes[2] == sizeof(long) && !X::same[0] &&
      X::same[1],
    "each element of R");
  __CPROVER_assert(X::sizes[2] == 1, "WRONG (must FAIL)");
  return 0;
}
