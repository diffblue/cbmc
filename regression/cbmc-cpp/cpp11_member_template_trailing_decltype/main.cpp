// Dog-food kernel (approximating src/util/options.cpp's
// make_range(option_map).map(lambda) `<<type:auto>>` failure): a
// member function template whose TRAILING RETURN TYPE names a data
// member and the lambda parameter (`auto map(F f) const ->
// decltype(f(*b_))`, [dcl.fct]/12 + [expr.prim.id.general]) fails to
// resolve ("found no match for symbol 'map'") when called on a
// two-level std::map-derived range.
#include <list>
#include <map>
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
template <class It> struct ranget
{
  It b_, e_;
  It begin() const
  {
    return b_;
  }
  It end() const
  {
    return e_;
  }
  template <class F> auto map(F f) const -> decltype(f(*b_))
  {
    return f(*b_);
  }
  template <class C> operator C() const
  {
    return C(begin(), end());
  }
};
template <class C> auto make_range(C &c) -> ranget<decltype(c.begin())>
{
  return ranget<decltype(c.begin())>{c.begin(), c.end()};
}
struct optionst
{
  typedef std::list<std::string> value_listt;
  typedef std::map<std::string, value_listt> option_mapt;
  option_mapt option_map;
  std::size_t to_json() const
  {
    return make_range(option_map).map(
      [](const std::pair<const std::string, value_listt> &p) {
        return p.second.size();
      });
  }
};
int main()
{
  optionst o;
  o.option_map["k"].push_back("v");
  __CPROVER_assert(o.to_json() == 1, "map over const two-level map");
  return 0;
}
