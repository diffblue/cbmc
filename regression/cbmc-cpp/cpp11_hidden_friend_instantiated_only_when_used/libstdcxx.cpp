#include <list>
#include <map>
#include <set>
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
// no operator<
struct value
{
  int v;
};
struct target_less
{
  bool operator()(std::list<int>::iterator a, std::list<int>::iterator b) const
  {
    return &*a < &*b;
  }
};
int main()
{
  // [temp.inst]/4: the containers' non-member operator< (lexicographical
  // comparison of the elements) is not used, so neither it nor the
  // element comparison it needs is instantiated
  std::map<std::string, value> m;
  m["a"] = value{1};
  __CPROVER_assert(m.size() == 1, "map with a non-comparable mapped type");
  std::list<int> l{1, 2};
  std::set<std::list<int>::iterator, target_less> s;
  s.insert(l.begin());
  __CPROVER_assert(s.size() == 1, "set of list iterators");
  __CPROVER_assert(s.size() == 2, "WRONG (must FAIL)");
}
