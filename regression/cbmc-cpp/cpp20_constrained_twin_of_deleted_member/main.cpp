// N5008 [over.match.best]/2.6 with [temp.constr.order]: two member functions
// with the same signature, one deleted and unconstrained and one with a
// trailing requires-clause (libstdc++'s C++20 std::pair: `pair
// &operator=(const pair &) = delete;' beside `constexpr pair &operator=(const
// pair &) requires (_S_assignable<const _T1 &, const _T2 &>())'); the
// constrained one is more constrained and is selected.  Look-up found the
// deleted one ("operator= is not accessible"), and the requires-clause's
// `( expression )' -- a call -- was not parsed at all ([temp.pre]: a
// primary-expression).  A constrained member whose constraints do not hold
// (pair<const int, int>'s move assignment) is not viable and its body is not
// instantiated ([temp.inst]/4): its failing conversion is no dropped body.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T1, class T2>
struct pair
{
  T1 first;
  T2 second;
  constexpr pair(T1 a, T2 b) : first(a), second(b)
  {
  }
  template <class U1, class U2>
  static constexpr bool assignable()
  {
    return __is_assignable(T1 &, U1) && __is_assignable(T2 &, U2);
  }
  pair &operator=(const pair &) = delete;
  constexpr pair &operator=(const pair &p)
    requires(assignable<const T1 &, const T2 &>())
  {
    first = p.first;
    second = p.second;
    return *this;
  }
  constexpr pair &operator=(pair &&p) requires(assignable<T1, T2>())
  {
    first = static_cast<T1 &&>(p.first);
    second = static_cast<T2 &&>(p.second);
    return *this;
  }
};
int main()
{
  pair<int, int> q(3, 4), r(0, 0);
  r = q;
  __CPROVER_assert(
    r.second == 4, "constrained operator= beats the deleted one");
  pair<int, int> m(5, 6);
  r = static_cast<pair<int, int> &&>(m);
  __CPROVER_assert(r.first == 5, "constrained move assignment");
  pair<const int, int> c(7, 8);
  __CPROVER_assert(
    c.first == 7, "const member pair: assignment not viable, not instantiated");
  __CPROVER_assert(r.second == 3, "WRONG (must FAIL)");
}
