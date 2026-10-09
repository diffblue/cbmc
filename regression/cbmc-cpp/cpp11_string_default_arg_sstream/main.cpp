// Regression for the implicit conversion `char[N]` -> `std::string`
// on a constructor default argument, when <sstream> (or any header
// that transitively triggers full elaboration of std::basic_string)
// is in the translation unit.
//
// Reduced from dog-fooding goto-cc on CBMC's own
// src/util/exception_utils.h:62
//   invalid_command_line_argument_exceptiont(
//     std::string reason,
//     std::string option,
//     std::string correct_input = "");
//
// The culprit is libstdc++'s basic_string constructor
//   template<typename = _RequireAllocator<_Alloc>>
//   basic_string(const _CharT* __s, const _Alloc& __a = _Alloc());
// This is a member *template* with a SFINAE guard and is therefore
// not elaborated into the struct's components list that
// user_defined_conversion_sequence iterates.  Without the
// fallback, `char[1]` -> `std::string` has no viable constructor
// in the components list, and CBMC emits
//   invalid implicit conversion from 'char [1l]' to 'struct basic_string'
//
// The fix in cpp_typecheck_conversions.cpp::implicit_typecast
// detects this specific pattern (source is a char array or pointer
// and target is a basic_string struct_tag) and synthesises a call
// to the `basic_string(const char*, size_type, const Alloc&)`
// constructor with a strlen-computed length, which IS in the
// components list.

#include <sstream>
#include <string>

class ex
{
public:
  ex(std::string reason = "");
};

ex::ex(std::string reason)
{
  (void)reason;
}

int main()
{
  ex e;
  return 0;
}
