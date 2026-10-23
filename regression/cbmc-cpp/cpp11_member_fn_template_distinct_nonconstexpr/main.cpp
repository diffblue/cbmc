// [temp.spec]/4 + [temp.inst]/2: each specialization of a member function
// template is a distinct entity -- including *non-constexpr* ones.  When the
// template parameters do not appear in the parameter types (e.g.
// `template<class U> static unsigned sz()` returning sizeof(U)), the
// specializations share one function signature, so CBMC used to name them all
// with the same unsuffixed member symbol; distinct specializations such as
// sz<char> and sz<int> then COLLIDED on one symbol and shared a single body
// (sz<int> returned 1, char's body -- unsound).
//
// A member function template specialization that has a body and no
// same-signature non-template overload now gets a distinct symbol that encodes
// its template arguments, so the specializations are independent entities -- at
// run time, not only in constant expressions.

struct TC
{
  // deliberately NOT constexpr
  template <class U>
  static unsigned sz()
  {
    return sizeof(U);
  }
};

int main()
{
  unsigned a = TC::sz<char>();
  unsigned b = TC::sz<int>();
  unsigned c = TC::sz<char[8]>();
  __CPROVER_assert(a == 1, "sz<char> == 1");
  __CPROVER_assert(b == sizeof(int), "sz<int> distinct entity");
  __CPROVER_assert(c == 8, "sz<char[8]> distinct entity");
  // non-vacuity: held only under the (unsound) collision -- must FAIL now.
  __CPROVER_assert(
    b == 1, "WRONG: sz<int>==1 only under collision (must FAIL)");
  return 0;
}
