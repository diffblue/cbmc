// A constexpr member of an explicit class-template specialization whose
// body is an arithmetic EXPRESSION (libstdc++'s
// numeric_limits<unsigned>::max(): `__INT_MAX__ * 2U + 1'), called in a
// constant expression inside a member of another class template.  The
// specialization's members are queued for the method-body drain; the
// constant-expression evaluator substituted the still un-type-checked body
// (its `*' and `+' carry no type) into the caller, which then failed with
// "conversion from '<<type:>>' ... implicit arithmetic conversion not
// permitted".  Every CBMC source file including <util/arith_tools.h>
// (numeric_castt's static_assert over numeric_limits) hit this.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct limits
{
  static constexpr T max() noexcept
  {
    return 7;
  }
};
template <>
struct limits<unsigned>
{
  static constexpr unsigned max() noexcept
  {
    return 2147483647 * 2U + 1;
  }
};
template <>
struct limits<long>
{
  static constexpr long max() noexcept
  {
    return 9223372036854775807L;
  }
};
template <class T>
struct checker
{
  bool in_static_assert() const
  {
    static_assert(limits<unsigned>::max() > 0, "in a template member");
    static_assert(limits<T>::max() > 0, "dependent");
    return true;
  }
  bool as_constexpr_variable() const
  {
    constexpr unsigned m = limits<unsigned>::max();
    static_assert(m == 4294967295U, "value");
    return m == 4294967295U;
  }
  bool at_run_time() const
  {
    return limits<unsigned>::max() == 4294967295U && limits<long>::max() > 0;
  }
};
int main()
{
  checker<unsigned> c;
  __CPROVER_assert(c.in_static_assert(), "static_assert");
  __CPROVER_assert(c.as_constexpr_variable(), "constexpr variable");
  __CPROVER_assert(c.at_run_time(), "run time");
  return 0;
}
