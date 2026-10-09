// C++20 optional features require GCC 10+
#if !defined(__GNUC__) && !defined(_MSC_VER) || __GNUC__ >= 10
// Test that basic STL headers work with system libc++ (Apple or LLVM).
// This exercises _Float16 handling, __decay builtin, and error recovery
// for parameter type mismatches in libc++ internals.
#  include <optional>
#  include <string>
#  include <vector>

int main()
{
  std::vector<int> v;
  v.push_back(42);
  __CPROVER_assert(v.size() == 1, "vector size");

  std::string s = "hello";
  __CPROVER_assert(s.size() == 5, "string size");

  std::optional<int> o = 7;
  __CPROVER_assert(o.has_value(), "optional has value");
}

#else
int main()
{
}
#endif
