// N5008 [over.match.funcs]/5, [over.match.best], [over.ics.ref]: for a call on
// a non-const object, an implicit-object parameter binding to a non-const
// member function is a better match than one binding to a const member
// function.  This ranking must apply to member function TEMPLATES too.
//
// libstdc++'s std::function depends on it: _Any_data has overloaded member
// function templates
//   template<class T> T& _M_access();              // non-const
//   template<class T> const T& _M_access() const;  // const
// and _Function_base::_Base_manager::_M_create does
//   __dest._M_access<_Functor*>() = new _Functor(...);
// on a non-const _Any_data, which must select the non-const _M_access (an
// lvalue) so the assignment is well-formed.
//
// Now handled: for a non-const object, overload resolution between a const and
// a non-const member function TEMPLATE selects the non-const one.  The deduced
// function type of an uninstantiated template_function_instance carries no
// `this` parameter, so the const member-qualifier is recovered from the
// candidate template's ID_method_qualifier and added to the cv distance (a
// const member function called on a non-const object ranks worse).
//
// Header-free and non-vacuous (assertion 2 must FAIL).

extern "C" void __CPROVER_assert(int, const char *);

struct S
{
  int y;
  template <class T>
  T &acc()
  {
    return *(T *)&y;
  }
  template <class T>
  const T &acc() const
  {
    return *(const T *)&y;
  }
};

int main()
{
  S s;
  s.acc<int>() = 5; // non-const s: must select non-const acc() (an lvalue)
  __CPROVER_assert(s.acc<int>() == 5, "non-const member template selected");
  __CPROVER_assert(s.acc<int>() == 6, "WRONG must FAIL");
  return 0;
}
