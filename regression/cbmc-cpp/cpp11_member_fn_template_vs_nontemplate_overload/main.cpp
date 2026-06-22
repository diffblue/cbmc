// [temp.spec]/4 + [over.match]: a member function template and a non-template
// member function may have the same signature (e.g. `unsigned f()` and
// `template<class U> unsigned f()`).  A call `f<U>()` with explicit template
// arguments selects the template ([temp.arg.explicit]); a call `f()` selects
// the non-template.  Each template specialization is a distinct entity
// ([temp.spec]/4), so f<char>() and f<int>() must be independent of each other
// and of the non-template f().
//
// CBMC named the template specializations with the same unsuffixed member
// symbol as the non-template overload, so f<char>(), f<int>() and f() all
// collided on one symbol and shared the non-template's body (returning 0 --
// unsound).  A value-dependent member function template specialization that
// shadows a same-signature non-template overload but whose own definition
// survives instantiation now gets a distinct symbol.  (When the definition
// does NOT survive instantiation -- as for some library type-erasure accessors
// -- the call still falls back to the non-template overload.)

struct TC
{
  unsigned f()
  {
    return 0;
  } // non-template overload

  template <class U>
  unsigned f() // value-dependent member function template
  {
    return sizeof(U);
  }
};

int main()
{
  TC t;
  unsigned a = t.f<char>();
  unsigned b = t.f<int>();
  unsigned n = t.f();
  __CPROVER_assert(a == 1, "f<char>() == 1");
  __CPROVER_assert(b == sizeof(int), "f<int>() distinct entity");
  __CPROVER_assert(n == 0, "non-template f() == 0");
  // non-vacuity: held only under the (unsound) collision -- must FAIL now.
  __CPROVER_assert(
    b == 0, "WRONG: f<int>()==0 only under collision (must FAIL)");
  return 0;
}
