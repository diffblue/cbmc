extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [stmt.ranged]/1: `for-range-declaration = *__begin;' -- a reference
// loop variable binds to the element; it was a by-value copy (writes through
// `auto &' were lost, `S &' produced a type-inconsistent assignment).
#include <list>
#include <vector>
struct S
{
  int v;
};
int main()
{
  int arr[3] = {1, 2, 3};
  for(auto &x : arr)
    x = 5;
  __CPROVER_assert(
    arr[0] == 5 && arr[2] == 5, "A: auto& over array writes through");
  S sarr[2] = {{1}, {2}};
  for(auto &s : sarr)
    s.v = 9;
  __CPROVER_assert(sarr[1].v == 9, "B: auto& struct over array");
  for(S &s : sarr)
    s.v = 4;
  __CPROVER_assert(sarr[0].v == 4, "C: S& over array");
  std::vector<int> vec = {1, 2};
  for(auto &x : vec)
    x = 7;
  __CPROVER_assert(vec[1] == 7, "D: auto& over vector writes through");
  std::list<int> ls[1];
  ls[0].push_back(1);
  for(const auto &l : ls)
    __CPROVER_assert(
      !l.empty() && l.front() == 1,
      "E: const auto& to a list element (no bitwise copy)");
  for(const std::list<int> &l : ls)
    __CPROVER_assert(l.size() == 1, "F: const T& to a list element");
  return 0;
}
