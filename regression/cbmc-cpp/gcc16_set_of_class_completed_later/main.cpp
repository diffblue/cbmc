// The shape of cpp11_set_of_class_completed_later against libstdc++ 16:
// `std::set<late>' named while `late' is only declared.  gcc 16's <set>
// reaches the node type through `_Node_traits<_Val, _Val *>::_Node' (a
// typedef of _Rb_tree_node<_Val>) and __rb_tree::_Node's union storage; the
// deferred instantiation that fixes the gcc 13 shape leaves this one with a
// node whose value pointers point outside the node ("pointer outside object
// bounds in this->v" in late::operator<), and the assertion fails.  Passes
// with gcc 11-15 headers.
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
