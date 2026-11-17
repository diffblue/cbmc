// libstdc++ 16 constructs a std::string from a `const char *' through the
// member template `_M_construct<bool _Copy>(const char *, size_type)'
// (basic_string.tcc; libstdc++ <= 14 had a non-template overload set).  The
// instantiation `_M_construct<1>' has no body ("no body for callee ...
// _M_construct<1>(this, ptr_const_char, ...)"), so every std::string built
// from a literal is nondeterministic.  Also behind the pair<const string,
// int> copy of cpp11_defaulted_copy_ctor_nontrivial_members and
// cpp_string_literal_const_type with gcc 15/16.
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  std::string s;
  explicit S(const std::string &x) : s(x)
  {
  }
};
int main()
{
  S a("abc");
  __CPROVER_assert(a.s.size() == 3, "string from a literal");
  return 0;
}
