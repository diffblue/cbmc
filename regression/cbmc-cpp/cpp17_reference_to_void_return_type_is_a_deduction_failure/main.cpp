// N5008 [temp.deduct.general]/8: type deduction fails if substituting the
// deduced (or explicit) template arguments forms an invalid type, e.g.
// "attempting to create a reference to void" (/8.1) -- in the RETURN type
// as much as in a parameter type.  `template <class T> T &&pick(int)' with
// T = void is dropped, and `T pick(long)' is selected -- libc++'s
// `declval<void>()' (`decltype(std::__declval<_Tp>(0))').  The front end
// only checked the parameter types and kept the `void &&' specialization.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
T &&pick(int);
template <class T>
T pick(long);
template <class T, class U>
constexpr bool same = false;
template <class T>
constexpr bool same<T, T> = true;
namespace lib
{
template <class T>
T &&__declval(int);
template <class T>
T __declval(long);
template <class T>
decltype(lib::__declval<T>(0)) declval() noexcept;
} // namespace lib
struct S
{
  int f(double) const;
};
int main()
{
  __CPROVER_assert(same<decltype(lib::declval<void>()), void>, "declval<void>");
  __CPROVER_assert(
    same<decltype(lib::declval<S>()), S &&>, "declval<S> is S&&");
  __CPROVER_assert(same<decltype(lib::declval<S &>()), S &>, "declval<S&>");
  __CPROVER_assert(
    same<decltype(lib::declval<const S &>().f(1.0)), int>,
    "member call on declval");
  __CPROVER_assert(
    same<decltype(pick<void>(0)), void>,
    "reference to void is a substitution failure");
  __CPROVER_assert(
    same<decltype(pick<int>(0)), int &&>, "int picks the int overload");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
