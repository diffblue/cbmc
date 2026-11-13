extern "C" void __CPROVER_assert(bool, const char *);
namespace chrono
{
struct month_day_last
{
  int d;
};
// [class.member.lookup]/3: outside a complete-class context the search for
// month_day_last is from the point of use, so the constructor's parameter
// names the class; the member function declared later does not change that
// declaration (libc++'s chrono::year_month_day_last)
struct year_month_day_last
{
  chrono::month_day_last mdl;
  year_month_day_last(const month_day_last &m) : mdl(m)
  {
  }
  year_month_day_last &operator+=(int k)
  {
    mdl.d += k;
    *this = *this;
    return *this;
  }
  chrono::month_day_last month_day_last() const
  {
    return mdl;
  }
};
} // namespace chrono
int main()
{
  chrono::year_month_day_last y{chrono::month_day_last{1}};
  y += 2;
  __CPROVER_assert(y.month_day_last().d == 3, "member function");
  __CPROVER_assert(y.month_day_last().d != 3, "WRONG (must FAIL)");
}
