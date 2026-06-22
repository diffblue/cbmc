// [temp.spec]/4 + [temp.inst]/2: each specialization of a member function
// template is a distinct entity.  When the template parameters do not appear
// in the parameter types -- e.g. `template<class U> static unsigned sz()`
// where U affects only the return value/body -- CBMC names every
// specialization with the same unsuffixed member symbol (the function
// signature, which omits the template arguments), so distinct specializations
// such as sz<char> and sz<int> COLLIDE on one symbol and share a single body.
//
// KNOWNBUG: the second assertion is expected to hold (sizeof(int) == 4), but
// because sz<int> collides with the earlier sz<char> instantiation it returns
// 1 (char's body), so verification currently FAILS.  This is unsound; it should
// be CORE once member function template specializations whose template
// arguments are not reflected in their parameter types get distinct symbols.
// (Constructors are unaffected: their template parameters are deduced from
// their parameter types, so the signature already distinguishes them.)

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
  return 0;
}
