// N5008 [meta.unary.prop]/9: is_constructible<T, U> holds iff `T
// t(declval<U>());' is well-formed -- DIRECT-initialization, for which an
// explicit constructor is a candidate ([dcl.init.general]/16.6.2,
// [over.match.ctor]).  The single-argument case was evaluated as a
// copy-initialization (an implicit conversion sequence), so the trait was
// false for `explicit saver(scopes &)', and std::optional<saver>::
// emplace(sc), constrained on it, had no viable overload ("instantiating
// 'std::enable_if_t' with <FALSE, ...>"; CBMC's own
// optional<cpp_save_scopet>, dog-fooding).  is_convertible stays false.
extern "C" void __CPROVER_assert(bool, const char *);
#include <optional>
#include <type_traits>
struct scopes
{
  int depth = 0;
};
class saver
{
public:
  explicit saver(scopes &s) : s(s), saved(s.depth)
  {
  }
  ~saver()
  {
    s.depth = saved;
  }

protected:
  scopes &s;
  int saved;
};
int main()
{
  static_assert(std::is_constructible_v<saver, scopes &>, "constructible");
  static_assert(
    !std::is_convertible_v<scopes &, saver>, "explicit: not convertible");
  static_assert(
    !std::is_constructible_v<saver, int>, "no matching constructor");
  static_assert(
    !std::is_constructible_v<saver, const scopes &>, "binding drops const");
  __CPROVER_assert(
    std::is_constructible_v<saver, scopes &>, "is_constructible");
  scopes sc;
  {
    std::optional<saver> o;
    o.emplace(sc);
    sc.depth = 5;
  }
  __CPROVER_assert(
    sc.depth == 0, "restored by the emplaced object's destructor");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
