extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  static constexpr int id = 5;
};
constexpr int S::id;
struct T
{
  static const int k = 6;
};
const int T::k;
const int *g = &S::id;
int main()
{
  const int *h = &T::k;
  __CPROVER_assert(
    *g == 5 && *h == 6 && g != h, "addresses of constant members");
  __CPROVER_assert(*g == 6, "WRONG (must FAIL)");
}
