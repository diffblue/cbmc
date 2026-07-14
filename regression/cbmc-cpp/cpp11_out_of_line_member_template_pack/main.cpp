// N5008 [temp.inst]/2, [temp.mem.func]: a member function template of a
// class template may be defined out of line; instantiating it uses that
// definition.  This is the shape of libstdc++'s
// _Rb_tree::_M_emplace_hint_unique (declared in the class, defined at the
// bottom of stl_tree.h), reached from std::map::operator[] -- the residual
// blocker of cpp20_map_basic / cpp11_map_insert.
//
// KNOWNBUG: with a parameter pack at arity >= 2, the instantiated member's
// body is lost ("no body for callee"), so the call returns nondet.  The
// out-of-line definition is not attached to the instantiated declarator (nil
// at typecheck_compound_declarator entry, probe-verified), unlike libstdc++'s
// case where the definition IS found but was then mishandled by the
// deferred-member drain (that second defect -- the fixpoint drain missing the
// function-template map restore and parameter-pack expansion of the main
// drain -- is FIXED; this attachment gap remains).  Arity 1 and non-pack
// member templates work.  g++ and clang++ accept and run this (asserts hold).
// Flip to CORE once the out-of-line definition is attached and converted.

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
