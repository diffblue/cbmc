extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [dcl.array]/5: the bound of an array of unknown bound declared with
// an initializer is the number of initializer-clauses; this holds for a
// static data member of a class template specialization, too
template <class... Ts>
struct S
{
  static constexpr bool b[] = {__is_same(Ts, int)...};
  static constexpr int c[] = {1, 2, 3};
};
int main()
{
  __CPROVER_assert(
    sizeof(S<int, char>::b) == 2 && S<int, char>::b[0] && !S<int, char>::b[1] &&
      sizeof(S<>::c) == 3 * sizeof(int),
    "bound from the initializer");
  __CPROVER_assert(sizeof(S<>::c) == sizeof(int), "WRONG (must FAIL)");
  return 0;
}
