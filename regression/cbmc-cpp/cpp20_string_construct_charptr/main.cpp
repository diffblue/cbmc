// KNOWNBUG (N5008 [temp.inst]/1-2, [dcl.typedef], [class.prop]).
//
// `std::string s("ab");` -- constructing a std::string from a string literal
// via its `basic_string(const _CharT*, const _Alloc&)` constructor.
//
// FRONT-END NON-CONFORMANCE (current): CBMC truncates `basic_string<char>` at
// its `const_reverse_iterator` member typedef
// (`reverse_iterator<const_iterator>`, whose eager definition-instantiation
// drives the C++20 iterator-concept chain and throws), dropping every later
// member including the constructors.  The class is then misclassified as a POD
// ([class.prop]) -- it has user-declared constructors and so is not a POD -- and
// `s("ab")` is routed to a bogus `char[3]` -> `basic_string` conversion
// ("CONVERSION ERROR").  Per [temp.inst]/2 and [dcl.typedef], naming the member
// typedef forms its (possibly incomplete) aliased type but does not require the
// aliased template's *definition*; truncating the whole class is non-conformant.
//
// A demonstrated fix (un-truncate by keeping the member typedef as a lazy alias)
// makes this conformant -- the constructors return, the class is non-POD, and
// `s("ab")` type-checks and reaches BMC -- but the *blanket* form also
// un-truncates std::vector/std::map and inlines their heavy header iterator
// machinery, which makes BMC of many container tests intractable.  The
// conformant-AND-tractable fix is the [temp.inst]/2 declarations-vs-definitions
// split (instantiate member *declarations*, keep member-function *definitions*
// lazy so BMC stays model-backed); that work is pending.
//
// Reclassify to CORE once the conformant front end lands and std::string
// construction is BMC-tractable.
// See doc/architectural/cpp-class-template-instantiation-plan.md.

#include <string>

int main()
{
  std::string s("ab");
  __CPROVER_assert(s.size() == 2, "string built from literal has size 2");
  return 0;
}
