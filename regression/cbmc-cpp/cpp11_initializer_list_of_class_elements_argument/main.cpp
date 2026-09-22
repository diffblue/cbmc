// N5008 [over.ics.list]/4-7: a braced-init-list argument for a parameter of
// type std::initializer_list<X> is viable when every element converts to X
// -- including elements that are themselves braced-init-lists,
// list-initializing X (an aggregate, a class with a matching constructor,
// std::pair).  The viability check only tried a plain conversion of the
// nested braces, so `f({{1, 2}, {3, 4}})' found no match -- std::map's and
// CBMC's json_objectt's `{{"key", value}, ...}' constructor calls.
#include <initializer_list>
#include <map>
#include <string>
#include <utility>
extern "C" void __CPROVER_assert(bool, const char *);

struct pointt
{
  int x, y;
  pointt(int a, int b) : x(a), y(b)
  {
  }
};
struct aggregatet
{
  int x, y;
};
int count_points(std::initializer_list<pointt> il)
{
  int s = 0;
  for(const auto &p : il)
    s += p.x + p.y;
  return s;
}
int count_aggregates(std::initializer_list<aggregatet> il)
{
  return il.size();
}
int count_pairs(std::initializer_list<std::pair<int, int>> il)
{
  int s = 0;
  for(const auto &p : il)
    s += p.first * p.second;
  return s;
}
struct jsont
{
  int kind;
  jsont() : kind(0)
  {
  }
  explicit jsont(int k) : kind(k)
  {
  }
};
struct json_objectt : jsont
{
  using objectt = std::map<std::string, jsont>;
  objectt object;
  json_objectt() : jsont(1)
  {
  }
  explicit json_objectt(
    std::initializer_list<typename objectt::value_type> &&il)
    : jsont(1), object{il}
  {
  }
  template <typename begin_iteratort, typename end_iteratort>
  json_objectt(begin_iteratort &&b, end_iteratort &&e)
    : jsont(1),
      object(std::forward<begin_iteratort>(b), std::forward<end_iteratort>(e))
  {
  }
};

int main()
{
  __CPROVER_assert(count_points({{1, 2}, {3, 4}}) == 10, "class elements");
  __CPROVER_assert(count_aggregates({{1, 2}, {3, 4}}) == 2, "aggregates");
  __CPROVER_assert(count_pairs({{1, 2}, {3, 4}}) == 14, "std::pair elements");
  json_objectt o({{"name", jsont(2)}, {"loc", jsont(3)}});
  __CPROVER_assert(o.object.size() == 2, "map value_type elements");
  __CPROVER_assert(o.object["loc"].kind == 3, "the entries");
  return 0;
}
