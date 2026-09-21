extern "C" void __CPROVER_assert(bool, const char *);
#include <list>
#include <utility>
// N5008 [stmt.ranged]/1: a range-based for is equivalent to a block that
// declares the for-range-declaration; the loop variable is scoped to the
// loop.  Two sequential loops may reuse the name with DIFFERENT types, and
// the name is free again after the loop.
struct L
{
  int n;
  bool empty() const
  {
    return n == 0;
  }
};
struct statet
{
  std::pair<int, std::pair<unsigned, L>> a[2];
  std::pair<int, std::list<int>> b[2];
  std::list<int> c;
};
int main()
{
  statet state;
  state.a[0] = {1, {2u, L{0}}};
  state.a[1] = {3, {4u, L{5}}};
  state.b[0] = {6, {}};
  state.b[1] = {7, {8}};
  state.c.push_back(10);
  state.c.push_back(20);
  int n = 0;
  for(const auto &pair : state.a) // pair<int, pair<unsigned, L>>
    if(pair.second.second.empty())
      n += pair.first;
  __CPROVER_assert(n == 1, "first loop");
  for(const auto &pair : state.b) // pair<int, list<int>>: same name, other type
    if(pair.second.empty())
      n += pair.first;
  __CPROVER_assert(n == 7, "second loop with the same variable name");
  for(const auto &pair : state.c) // int: class range, same name again
    n += pair;
  __CPROVER_assert(n == 37, "third loop (class range) with the same name");
  int pair = 100; // the name is free after the loops
  __CPROVER_assert(pair == 100, "redeclared after the loops");
  for(int i : {1, 2})
    n += i;
  for(int i : {3, 4})
    n += i;
  __CPROVER_assert(n == 47, "initializer-list ranges with the same name");
  return 0;
}
