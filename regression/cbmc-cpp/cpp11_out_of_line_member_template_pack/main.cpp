// N5008 [temp.inst]/2, [temp.mem.func]: a member function template of a
// class template may be defined out of line; instantiating it uses that
// definition.  This is the shape of libstdc++'s
// _Rb_tree::_M_emplace_hint_unique (declared in the class, defined at the
// bottom of stl_tree.h), reached from std::map::operator[] -- the residual
// blocker of cpp20_map_basic / cpp11_map_insert.
//
// FIXED: the out-of-line definition (recorded as a template_methods entry of
// the enclosing class template) is now attached to the instantiated
// member-template declarator -- with the owning class template matched, so a
// same-named member of an unrelated template is not adopted -- and the
// definition's parameter names are used so its body binds ([dcl.fct]/3).

extern "C" void __CPROVER_assert(int, const char *);

template<typename K>
struct tree
{
  int stored;
  tree() : stored(0)
  {
  }
  template<typename... Args>
  int emplace(Args... args); // defined out of line below
  template<typename U0, typename... R>
  static int first_of(U0 u0, R...)
  {
    return (int)u0;
  }
};

template<typename K>
template<typename... Args>
int tree<K>::emplace(Args... args)
{
  stored = first_of(args...);
  return stored;
}

int main()
{
  tree<int> t;
  __CPROVER_assert(t.emplace(7, 8.0) == 7, "out-of-line pack body runs");
  __CPROVER_assert(t.stored == 7, "member updated");
  return 0;
}
