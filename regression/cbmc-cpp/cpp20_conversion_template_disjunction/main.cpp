// [temp.constr.op]: a disjunction of constraints is satisfied iff either
// operand is.  A conversion-function template whose requires-clause is a
// disjunction (here integral<T> || floating_point<T>) must, per [temp.deduct]/5,
// be removed from the candidate set when the *whole* constraint is unsatisfied
// with the deduced arguments -- which for a class destination T means BOTH
// disjuncts are false.
//
// This is the shape of libstdc++'s __max_size_type / __max_diff_type templated
// conversion operators, whose constraint is integral<_Tp> || __is_int128<_Tp>.
// Deducing such an operator for the mutually-recursive class destination must
// fail, otherwise the front end instantiates a bogus "operator <class>".
#include <concepts>

namespace d
{
class MD;
class MS
{
public:
  unsigned long _M_val = 0;
  MS() = default;
  template <typename T>
    requires(std::integral<T> || std::floating_point<T>)
  constexpr MS(T i) noexcept : _M_val((unsigned long)i)
  {
  }
  constexpr explicit MS(const MD &dd) noexcept;
  template <typename T>
    requires(std::integral<T> || std::floating_point<T>)
  constexpr explicit operator T() const noexcept
  {
    return _M_val;
  }
};
class MD
{
public:
  MS _M_rep;
  MD() = default;
  template <typename T>
    requires(std::integral<T> || std::floating_point<T>)
  constexpr MD(T i) noexcept : _M_rep(i)
  {
  }
  constexpr explicit MD(const MS &dd) noexcept : _M_rep(dd)
  {
  }
  template <typename T>
    requires(std::integral<T> || std::floating_point<T>)
  constexpr explicit operator T() const noexcept
  {
    return static_cast<T>(_M_rep);
  }
};
constexpr MS::MS(const MD &dd) noexcept : _M_val(dd._M_rep._M_val)
{
}
}

int main()
{
  d::MD md{5};
  int x = (int)md;
  __CPROVER_assert(x == 5, "disjunction-constrained conversion operator");
  return 0;
}
