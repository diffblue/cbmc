// Unit proof for string2optional_int (src/util/string2int.cpp).
//
// Where the unit tests spot-check fixed samples, this harness proves,
// for ALL integers in a bounded domain (nondeterministic choice):
//  * round trip: unsafe_string2int(std::to_string(v)) == v;
//  * string2optional_int accepts the same string with the same value;
//  * stoi/stoll PREFIX semantics: a trailing non-digit is ignored, the
//    numeric prefix is converted (the function uses no endptr check);
//  * a string with NO digits at all yields nullopt (invalid_argument).
// Single translation unit: include the implementation directly.
#include <util/string2int.h>

#include "../../../src/util/string2int.cpp" // NOLINT

extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void __CPROVER_assume(bool);
int __VERIFIER_nondet_int();

int main()
{
  int v = __VERIFIER_nondet_int();
  __CPROVER_assume(v >= -999 && v <= 999);

  std::string s = std::to_string(v);

  __CPROVER_assert(unsafe_string2int(s) == v, "round trip");

  auto o = string2optional_int(s);
  __CPROVER_assert(o.has_value() && *o == v, "optional round trip");

  std::string tail = s + "x";
  auto p = string2optional_int(tail);
  __CPROVER_assert(
    p.has_value() && *p == v, "prefix converted, trailing junk ignored");

  auto none = string2optional_int("x");
  __CPROVER_assert(!none.has_value(), "no digits yields nullopt");

  return 0;
}
