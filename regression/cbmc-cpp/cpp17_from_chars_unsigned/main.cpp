// std::from_chars for an unsigned integer (libstdc++'s
// `__integer_from_chars_result_type<_Tp>' = enable_if_t<__or_<
// __is_signed_integer<_Tp>, __is_unsigned_integer<_Tp>, is_same<char,
// _Tp>>::value, from_chars_result>): the __or_ of a false and a true
// alternative evaluated to false_type, so no overload was viable
// (string2optional<unsigned> in CBMC's own src/util/config.cpp).
#include <charconv>
#include <optional>
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
template <typename T>
std::optional<T> string2optional(const std::string &str, int base)
{
  T result;
  auto res = std::from_chars(str.data(), str.data() + str.size(), result, base);
  if(res.ec == std::errc{} && res.ptr == str.data() + str.size())
    return result;
  return std::nullopt;
}
int main()
{
  auto v = string2optional<unsigned>("42", 10);
  __CPROVER_assert(v.has_value() && *v == 42, "from_chars");
  auto w = string2optional<unsigned>("4x", 10);
  __CPROVER_assert(!w.has_value(), "from_chars fail");
}
