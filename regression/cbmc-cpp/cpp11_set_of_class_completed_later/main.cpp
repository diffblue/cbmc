// N5008 [temp.inst]/1-2: naming `std::set<late>' (a declaration and an
// inline function that only default-constructs one) while `late' is still an
// incomplete class must not instantiate the node type -- libstdc++'s
// _Rb_tree_node<late> has `unsigned char _M_storage[sizeof(late)]'.  The
// front-end instantiated it through `typedef _Rb_tree_node<_Val> *_Link_type'
// and the allocator rebind's template argument, failed on the sizeof, and
// left the node type empty for good (CBMC's find_symbols.h declares
// `std::set<symbol_exprt>' with symbol_exprt forward-declared).  A pointer
// declarator, a member function declaration and a template argument do not
// require completeness.
#include <set>
extern "C" void __CPROVER_assert(bool, const char *);
class late; // complete only after the container instance is named
std::set<late> make_set();
inline std::set<late> wrap()
{
  std::set<late> s;
  return s;
}
class late
{
public:
  int v;
  bool operator<(const late &o) const
  {
    return v < o.v;
  }
};
std::set<late> make_set()
{
  std::set<late> s;
  s.insert(late{3});
  s.insert(late{1});
  return s;
}
int main()
{
  std::set<late> s = make_set();
  __CPROVER_assert(s.size() == 2 && s.begin()->v == 1, "set of a late class");
  return 0;
}
