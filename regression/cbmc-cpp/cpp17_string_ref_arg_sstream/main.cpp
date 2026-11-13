// Regression for the implicit conversion `char[N]` -> `const std::string&`
// (reference binding to a function parameter), when <sstream> is in
// the translation unit.  Sister test to cpp11_string_default_arg_sstream
// which covers the same conversion in default-argument context.
//
// Reduced from dog-fooding goto-cc on CBMC's own
// src/util/invariant.h:275
//   void invariant_violated_string(
//     const std::string &file,
//     const std::string &function,
//     int line,
//     const std::string &condition,
//     const std::string &reason);
// PRECONDITION(...) expands to a call to this function with five
// `char[N]` literal arguments.
//
// The culprit is libstdc++'s basic_string converting constructor
//   template<typename = _RequireAllocator<_Alloc>>
//   basic_string(const _CharT* __s, const _Alloc& __a = _Alloc());
// — a member template with a SFINAE guard.  CBMC's class
// elaboration drops it from the components list when later
// libstdc++ headers (e.g. <bits/locale_classes.h>, included by
// <sstream> via <ios>) re-elaborate basic_string<char>.  Without
// the fallback, `char[N]` -> `const std::string&` reference
// binding has no viable converting constructor, and CBMC emits
//   found no match for symbol 'take'
//
// The fix in cpp_typecheck_conversions.cpp::user_defined_conversion_sequence
// mirrors the existing implicit_typecast workaround: detect this
// specific pattern (source char-array / char-pointer, target
// basic_string struct_tag) and synthesise a call to the 4-arg
// `basic_string(const char*, size_type, const Alloc&)` ctor which
// IS reliably present in the components list.

#include <sstream>
#include <string>

void take(const std::string &a, const std::string &b);

void take(const std::string &a, const std::string &b)
{
  (void)a;
  (void)b;
}

int main()
{
  take("hello", "world");
  return 0;
}
