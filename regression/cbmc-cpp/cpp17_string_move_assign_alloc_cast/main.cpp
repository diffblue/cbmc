// Move-assigning a std::string from a temporary reaches libstdc++'s
// allocator-propagation helpers, which access the string's EBO
// allocator base through a reinterpreted pointer
// ((__new_allocator<char> *)&s).  The dereference is lowered to a
// struct VALUE typecast -- (std::__new_allocator<char>)<basic_string
// struct value> -- which the bit-blaster cannot convert:
// boolbvt::conversion_failed havocs the value and prints
// "warning: ignoring typecast".  Here the havocked value is an EMPTY
// (stateless) allocator, so the result happens to be unaffected, but
// a dropped constraint is a soundness hole in general: the front end
// or the dereference lowering should produce a base-component
// extraction (or an empty-struct constant) instead.
// Found by the trim_from_last_delimiter unit proof's soundness gate.
// g++/clang++ accept and verify at runtime.
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::string s = "x.y";
  std::string result;
  result = s.substr(0, 1); // move-assignment from a temporary
  __CPROVER_assert(result == "x", "assigned prefix");
  return 0;
}
