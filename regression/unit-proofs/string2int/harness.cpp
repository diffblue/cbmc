// Unit proof for unsafe_string2int (src/util/string2int.cpp).
//
// Where the unit tests spot-check fixed samples, this harness proves
// the decimal round trip unsafe_string2int(std::to_string(v)) == v for
// ALL integers in a bounded domain (nondeterministic choice).  It
// exercises std::to_string and the new strtoll library model
// end-to-end.  The string2optional layer is covered by the KNOWNBUG
// proof in ../string2optional.
// Single translation unit: include the implementation directly.
#include <util/string2int.h>

#include "../../../src/util/string2int.cpp"

extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void __CPROVER_assume(bool);
int __VERIFIER_nondet_int();

int main()
{
  int v = __VERIFIER_nondet_int();
  __CPROVER_assume(v >= -999 && v <= 999);

  std::string s = std::to_string(v);

  __CPROVER_assert(unsafe_string2int(s) == v, "round trip");

  return 0;
}
