// Regression test: std::string fill construction std::string(n, c).
//
// std::string s(3, 'x') dispatches to
// basic_string<char>::_M_construct(size_type, _CharT).  For the explicitly
// instantiated basic_string<char>, that out-of-line member used to be
// attached the *wrong* overload's body (the input-iterator _M_construct,
// which refers to `__beg`) by a base-name-only match, so its conversion
// failed and the constructor became a no-op (both size() and the characters
// were wrong).
//
// convert_function now repairs such a member by adopting the out-of-line
// definition whose signature (parameter arity) matches it, together with that
// definition's parameter names ([dcl.fct]/3), so the fill constructor sets the
// length and fills the buffer.  Grounded in N5008 [over.match] + [dcl.fct]/3.
// See doc/architectural/cpp-extern-template-member-instantiation.md.

#include <string>

int main()
{
  std::string s(3, 'x');

  __CPROVER_assert(s.size() == 3, "size() == 3");
  __CPROVER_assert(s[0] == 'x', "s[0] == 'x'");

  return 0;
}
