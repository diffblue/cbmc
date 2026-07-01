// N5008 [temp.expl.spec]/2: an explicit specialization of a class template may
// be declared with a qualified-id naming the template, from any namespace that
// encloses the template's.  Here `ns::G<char>` is specialized from the global
// scope.  The specialization (v()==2) must be selected for G<char>, not the
// primary template (v()==1).  g++/clang++ agree.
//
// This is the mechanism behind specializing std::hash for a user type outside
// namespace std (`template <> struct std::hash<T> { ... };`), which is required
// for user types to be usable as keys in std::unordered_map/set.
//
// assertion.2 must FAIL, proving assertion.1 is non-vacuous (a stubbed-out call
// returning nondet would let both pass).

extern "C" void __CPROVER_assert(int, const char *);

namespace ns
{
template <class T>
struct G
{
  int v() const
  {
    return 1;
  }
};
} // namespace ns

// Explicit specialization named with a qualified-id, from the global scope.
template <>
struct ns::G<char>
{
  int v() const
  {
    return 2;
  }
};

int main()
{
  ns::G<char> g;
  ns::G<int> gi;
  __CPROVER_assert(g.v() == 2, "qualified explicit specialization selected");
  __CPROVER_assert(gi.v() == 1, "primary template used for non-specialized arg");
  __CPROVER_assert(g.v() == 1, "WRONG must FAIL");
  return 0;
}
