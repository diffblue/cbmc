// KNOWNBUG: std::string fill-construction is a complete no-op.
//
// std::string s(3, 'x') dispatches to basic_string<char>::_M_construct(
// size_type, char).  For the explicitly-instantiated basic_string<char>
// (extern template), that member is realised as a *declaration only* — its
// body is never instantiated (it sits in deferred_typechecking with a nil
// body and is discarded by cpp_typecheckt::clean_up()).  The constructor
// therefore neither sets the length nor fills the buffer, so BOTH size()
// and the character contents are wrong (unlike the literal-construction
// case, where only the characters are wrong).
//
// This is the same underlying gap as cpp11_string_literal_char_access:
// the elaborate-only realisation path that basic_string<char> takes does
// not convert deferred inline member bodies.  Grounded in N5008
// [temp.inst]/4 and Note 4.  When fixed, reclassify from KNOWNBUG to CORE.

#include <string>

int main()
{
  std::string s(3, 'x');

  __CPROVER_assert(s.size() == 3, "size() == 3");
  __CPROVER_assert(s[0] == 'x', "s[0] == 'x'");

  return 0;
}
