// Constant evaluation of libc++'s <tuple> `__find_exactly_one_checked'
// shape: a constexpr static member ARRAY initialised from a pack expansion
// (N5008 [dcl.constexpr]/6 makes it const), read by a recursive constexpr
// function taking a REFERENCE TO ARRAY (`const bool (&)[N]', [dcl.init.ref])
// whose `size_t' arguments arrive converted ([conv.integral]).  Three gaps:
// the member array had lost its const, the reference parameter denoted the
// first element instead of the array, and a converted scalar argument was
// not folded to its constant.
extern "C" void __CPROVER_assert(bool, const char *);
using size_t = decltype(sizeof(int));
template <class T, class U>
struct is_same
{
  static constexpr bool value = __is_same(T, U);
};
namespace fd
{
static constexpr size_t not_found = static_cast<size_t>(-1);
static constexpr size_t ambiguous = not_found - 1;
inline constexpr size_t idx_return(size_t curr, size_t res, bool matches)
{
  return !matches ? res : (res == not_found ? curr : ambiguous);
}
template <size_t N>
inline constexpr size_t find_idx(size_t i, const bool (&matches)[N])
{
  return i == N ? not_found
                : fd::idx_return(i, fd::find_idx(i + 1, matches), matches[i]);
}
template <class T1, class... Args>
struct checked
{
  static constexpr bool matches[sizeof...(Args)] = {
    is_same<T1, Args>::value...};
  static constexpr size_t value = fd::find_idx(0, matches);
  static_assert(value != not_found, "type not found in type list");
  static_assert(value != ambiguous, "type occurs more than once in type list");
};
} // namespace fd
template <class T1, class... Args>
struct find_one : public fd::checked<T1, Args...>
{
};
constexpr bool m01[2] = {false, true};
constexpr size_t first_true(const bool (&m)[2])
{
  return m[1] ? 1 : 0;
}
constexpr unsigned long identity(unsigned long r)
{
  return r;
}
static_assert(identity(7) == 7, "[conv.integral] on the argument");
static_assert(first_true(m01) == 1, "reference to array parameter");
static_assert(fd::find_idx(0, m01) == 1, "recursive, deduced bound");
static_assert(fd::checked<double, int, double>::matches[1], "member array");
static_assert(find_one<int, int, double>::value == 0, "find int");
static_assert(find_one<double, int, double>::value == 1, "find double");
int main()
{
  __CPROVER_assert(
    find_one<double, int, double, char>::value == 1, "run-time read");
  __CPROVER_assert(
    find_one<double, int, double>::value == 0, "WRONG (must FAIL)");
}
