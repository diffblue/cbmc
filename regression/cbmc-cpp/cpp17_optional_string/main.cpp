// C++17 std::optional<std::string> construction from a string literal.
//
// KNOWNBUG (front-end CRASH): converting the constructor chain of
// libstdc++'s optional (the _Optional_payload/_Optional_base member
// initializers) reaches cpp_typecheckt::make_ptr_typecast with source and
// destination structs that are not in a base/derived relation, tripping
// its precondition (invariant violation, cpp_typecheck_compound_type.cpp
// make_ptr_typecast) instead of reporting or handling the conversion.
// Call chain at the crash (gdb): typecheck_member_initializer ->
// make_ptr_typecast, inside instantiate_template of an optional internal.
//
// Found by dog-fooding CBMC's own sources (util/simplify_expr.cpp and
// util/cmdline.cpp both crashed with this signature; both use
// std::optional<std::string>).  optional<int> works
// (cpp17_optional_basic).  Flip to CORE when the constructor chain
// converts.
extern "C" void __CPROVER_assert(bool, const char *);
#include <optional>
#include <string>

int main()
{
  std::optional<std::string> o("x");
  __CPROVER_assert(o.has_value(), "has value");
  __CPROVER_assert((*o)[0] == 'x', "value");
  return 0;
}
