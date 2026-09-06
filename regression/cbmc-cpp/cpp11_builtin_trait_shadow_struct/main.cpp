// Revertible builtin type-trait identifiers: GCC >= 14 and clang
// provide builtin traits named __make_unsigned, __remove_pointer,
// etc., yet libstdc++ (and libc++) STILL define fallback structs with
// those very names.  Real compilers make the keyword revertible:
// gcc lexes the builtin only when the identifier is directly followed
// by '(' ; clang demotes the keyword to an identifier on a shadowing
// declaration (-Wkeyword-compat warning).  CBMC's scanner keywords
// them unconditionally in CLANG mode / gcc14 mode, so parsing
// libstdc++-14's <type_traits> fails:
//   parse error before '__make_unsigned { using __type'
// (found by running the regression suite in a fedora:41 container,
// gcc 14.3 headers; host-reproducible with --stdlib libc++).
// CBMC already implements the followed-by-'(' discipline for
// __is_referenceable -- the same lookahead is needed for the whole
// revertible-trait family.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T> struct __make_unsigned
{
  using __type = T;
};
template <> struct __make_unsigned<char>
{
  using __type = unsigned char;
};
int main()
{
  __make_unsigned<char>::__type c = 255;
  __CPROVER_assert(c == 255, "shadowing struct named like a builtin trait");
  return 0;
}
