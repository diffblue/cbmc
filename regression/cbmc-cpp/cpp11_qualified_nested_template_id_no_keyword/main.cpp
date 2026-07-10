// N5008 [temp.names]/5: the `template` keyword before a member template-id is
// only REQUIRED when the nested-name-specifier is dependent on a template
// parameter.  For a NON-dependent qualified-id -- e.g. naming a member of the
// concrete class-template specialization `C<int>` -- it is optional; g++ and
// clang++ accept the program without it.
//
// Regression (parser): CBMC's expression name parser (rVarNameCore) used to be
// unable to parse a qualified-id whose nested-name-specifier is a
// class-template-id and whose next component is itself a member template-id,
// when the disambiguating `template` keyword is absent:
//
//   C<int>::al<char>::value        // was: parse error before '> :: value'
//   C<int>::template al<char>::value   // always parsed (keyword present)
//
// The bug was independent of what the inner member is: it fired for a member
// alias template (`using al = ...`) and for a nested class template
// (`struct N { ... };`) alike, and for a single inner argument (no parameter
// pack needed).  It required the OUTER name to be a class-template-id
// (`C<int>`); with a non-template outer class (`C::al<char>::value`) the same
// form parsed fine.  Two causes, both fixed in rVarNameCore: (1) the
// speculative template-argument check did not accept a following `::` (a
// `name<...>::` nested-name-specifier can only be a template-id), and (2) it
// treated every template-id qualifier as dependent, whereas a concrete
// instantiation like `C<int>` is not dependent -- it now mirrors rName by
// checking whether the qualifier's arguments involve a template parameter.
//
// This is the shape of libstdc++'s std::tuple constraint access
// `_TupleConstraints<_Types...>::__constructible<_UTypes...>`; libstdc++ writes
// it WITH the `template` keyword (the nested-name-specifier there is dependent),
// so std::tuple itself does not hit this bug -- but the unqualified form is
// well-formed C++ that CBMC previously rejected.
//
// Non-vacuity: assertion 2 distinguishes `al<char>` (P<char>::value == true)
// from `al<int>` (P<int>::value == false), so a correct parse must resolve the
// inner template argument, not merely accept the syntax.

extern "C" void __CPROVER_assert(int, const char *);

template <class>
struct P
{
  static constexpr bool value = false;
};
template <>
struct P<char>
{
  static constexpr bool value = true;
};

template <class T>
struct C
{
  template <class A>
  using al = P<A>;
};

int main()
{
  __CPROVER_assert(
    C<int>::al<char>::value,
    "member template-id after non-dependent class-template-id (true case)");
  __CPROVER_assert(
    !C<int>::al<int>::value,
    "member template-id after non-dependent class-template-id (false case)");
  return 0;
}
