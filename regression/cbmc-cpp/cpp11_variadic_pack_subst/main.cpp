// Regression test: variadic template pack expansion must use the full
// struct_tag identifier (with namespace and `tag-` markers) for nested
// template types like std::basic_string<char, char_traits<char>,
// allocator<char>>, where naive `::` splitting would land inside the
// nested template arguments.
//
// Before the fix, instantiating invariant_violated_structured with
// Params=std::string would fail with:
//   "symbol 'tag-allocator<char>>' is unknown"
// because the `rfind("::")` in the pack-substitution code naively
// found the `::` inside `std::tag-allocator<char>` template argument.

#include <string>
#include <type_traits>

struct invariant_failedt
{
  invariant_failedt(
    const std::string &file,
    const std::string &function,
    const int line,
    const std::string &backtrace,
    const std::string &condition,
    const std::string &reason)
  {
  }
};

template <class ET, typename... Params>
typename std::enable_if<std::is_base_of<invariant_failedt, ET>::value>::type
invariant_violated_structured(
  const std::string &file,
  const std::string &function,
  const int line,
  const std::string &condition,
  Params &&...params)
{
  ET to_throw(
    file, function, line, "bt", condition, std::forward<Params>(params)...);
}

inline void invariant_violated_string(
  const std::string &file,
  const std::string &function,
  const int line,
  const std::string &condition,
  const std::string &reason)
{
  invariant_violated_structured<invariant_failedt>(
    file, function, line, condition, reason);
}

int main()
{
  invariant_violated_string("file", "function", 1, "cond", "reason");
  return 0;
}
