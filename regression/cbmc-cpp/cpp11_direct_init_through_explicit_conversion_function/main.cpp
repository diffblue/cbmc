// N5008 [over.match.copy]/1.2: in the direct-initialization of a T, the
// copy constructor's `const T &' parameter may bind to the result of an
// explicit conversion function `operator T()'; copy-initialization does
// not consider it
#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);
struct days
{
  int n;
};
// libc++'s chrono::time_point, local_days and year_month_day
template <class Clock>
struct time_point
{
  days d;
  time_point() : d{0}
  {
  }
  explicit time_point(const days &x) : d(x)
  {
  }
};
struct sys_t
{
};
struct local_t
{
};
typedef time_point<sys_t> sys_days;
typedef time_point<local_t> local_days;
struct year_month_day
{
  int v;
  operator sys_days() const
  {
    return sys_days{days{v}};
  }
  explicit operator local_days() const
  {
    return local_days{days{v + 1}};
  }
};
struct year_month_day_last
{
  int v;
  explicit operator local_days() const
  {
    return local_days{year_month_day{v}};
  }
};
int main()
{
  year_month_day m{7};
  local_days a{m};
  local_days b(m);
  __CPROVER_assert(a.d.n == 8 && b.d.n == 8, "direct-initialization");
  sys_days s = m;
  __CPROVER_assert(s.d.n == 7, "implicit conversion function");
  year_month_day_last l{4};
  __CPROVER_assert(
    static_cast<local_days>(l).d.n == 5, "inside a conversion function");
  __CPROVER_assert(
    !std::is_convertible<year_month_day, local_days>::value,
    "not for copy-initialization");
  __CPROVER_assert(a.d.n == 7, "WRONG (must FAIL)");
}
