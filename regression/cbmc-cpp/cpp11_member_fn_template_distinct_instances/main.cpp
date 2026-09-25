// [temp.spec]/4 + [temp.inst]/2: each specialization of a member function
// template is a distinct entity.  When the template parameters do not appear
// in the parameter types -- e.g. `template<class U> static constexpr unsigned
// sz()` where U affects only the return value/body -- the specializations
// share one function signature, so CBMC used to name them all with the same
// unsuffixed member symbol; distinct specializations such as sz<char> and
// sz<int> then COLLIDED on one symbol and shared a single body (sz<int>
// returned 1, char's body -- unsound).
//
// A constexpr member function template specialization is now given a distinct
// symbol that encodes its template arguments, so the specializations are
// independent entities.  This is the shape of std::get<N>(tuple),
// std::tuple_element, etc.

struct TC
{
  template <class U>
  static constexpr unsigned sz()
  {
    return sizeof(U);
  }
};

int main()
{
  unsigned a = TC::sz<char>();
  unsigned b = TC::sz<int>();
  __CPROVER_assert(a == 1, "sz<char> == 1");
  __CPROVER_assert(
    b == sizeof(int), "sz<int> == sizeof(int) (distinct entity)");
  // non-vacuity: would hold only under the (unsound) collision, so it must FAIL
  // now that the specializations are distinct.
  __CPROVER_assert(
    b == 1, "WRONG: sz<int>==1 only under collision (must FAIL)");
  return 0;
}
