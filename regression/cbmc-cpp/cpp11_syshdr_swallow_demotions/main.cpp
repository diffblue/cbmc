// Witness for the system-header "report error without throwing" swallow:
// several recovery paths under convert_function's null-handler guard print
// a diagnostic and continue, leaving HALF-type-checked bodies; the final
// soundness sweep then demotes them ("inconsistent return ... body is
// dropped").  The program still verifies -- the demoted bodies havoc
// soundly -- but each demotion is lost precision, and on some address
// layouts enough bodies demote to push BMC past practical time (the
// cpp11_regex_match shape).  This test pins the MINIMAL trigger
// (std::to_string over libstdc++ <string>) and fails while ANY demotion
// warning is emitted; it flips to CORE when the swallow sites are fixed
// to throw or recover type-consistently.
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::string s = std::to_string(42);
  __CPROVER_assert(s.size() == 2, "to_string size");
  __CPROVER_assert(s[0] == '4' && s[1] == '2', "to_string digits");
  return 0;
}
