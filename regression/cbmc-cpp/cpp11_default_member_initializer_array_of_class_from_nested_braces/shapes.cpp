extern "C" void __CPROVER_assert(bool, const char *);
struct pr
{
  char first;
  int second;
  pr(char c, int t) : first(c), second(t)
  {
  }
};
struct agg
{
  int x, y;
};
struct S
{
  int a[3] = {1, 2, 3};
  int m[2][2] = {{1, 2}, {3, 4}};
  int e[2][2] = {5, 6, 7, 8};
  int part[3] = {9};
  agg g[2] = {{1, 2}, {3, 4}};
  pr p[2] = {{'a', 1}, {'b', 2}};
  char s[4] = "abc";
};
int main()
{
  S v;
  __CPROVER_assert(
    v.a[2] == 3 && v.m[1][0] == 3 && v.e[1][1] == 8 && v.part[0] == 9 &&
      v.part[2] == 0 && v.g[1].x == 3 && v.p[1].second == 2 && v.s[1] == 'b',
    "array default member initializers");
  __CPROVER_assert(v.p[0].first == 'b', "WRONG (must FAIL)");
}
