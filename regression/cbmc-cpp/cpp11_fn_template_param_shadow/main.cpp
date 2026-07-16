// N5008 [temp.deduct]/5 + [basic.scope.temp]/2: deducing a (member)
// function template binds only THAT template's own parameters; a
// same-short-name parameter of an unrelated enclosing template must be
// neither bound, nor conflict-checked, nor substituted into the deduced
// declaration.
//
// Regression (the std::chrono::duration mixed-period operator+ shape,
// header-free): the free function template's parameter `P2` (bound to
// ratio<1,1> by the caller) collided with the member converting
// constructor template's own `P2` (deduced ratio<60,1>); the flat-map
// short-name substitution baked the caller's binding into the deduced
// constructor signature, the constructor vanished from the overload set,
// and the function body was dropped (nondet result).  A same-named
// parameter with a COINCIDING value (R2 = long here) masked the defect.
//
// g++/clang++ verify all values at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

template <long N, long D = 1>
struct ratio
{
  static constexpr long num = N;
  static constexpr long den = D;
};
template <typename R, typename P>
struct duration;
template <typename ToDur, typename R, typename P>
constexpr ToDur duration_cast(const duration<R, P> &d);
template <typename R, typename P>
struct duration
{
  typedef R rep;
  typedef P period;
  R r;
  constexpr duration() : r(0)
  {
  }
  constexpr explicit duration(R v) : r(v)
  {
  }
  // member template with parameters named R2/P2
  template <typename R2, typename P2>
  constexpr duration(const duration<R2, P2> &d)
    : r(duration_cast<duration>(d).count())
  {
  }
  constexpr R count() const
  {
    return r;
  }
};
template <typename ToDur, typename R, typename P>
constexpr ToDur duration_cast(const duration<R, P> &d)
{
  return ToDur(static_cast<typename ToDur::rep>(
    d.count() * (P::num * ToDur::period::den) /
    (P::den * ToDur::period::num)));
}

// enclosing fn template parameters named R2/P2 too ([basic.scope.temp]/2:
// distinct parameters despite equal short names); P2 is defaulted and NOT
// deducible, so its binding (ratio<1,1>) differs from the ctor's deduced
// P2 (ratio<60,1>)
template <typename R2, typename P1, typename P2 = ratio<1>>
constexpr duration<R2, ratio<1, 1>> to_sec(const duration<R2, P1> &x)
{
  typedef duration<R2, ratio<1, 1>> cd;
  return cd(x);
}

template <typename R1, typename P1, typename R2, typename P2>
constexpr duration<R1, ratio<1, 1>>
add_secs(const duration<R1, P1> &lhs, const duration<R2, P2> &rhs)
{
  typedef duration<R1, ratio<1, 1>> cd;
  return cd(cd(lhs).count() + cd(rhs).count());
}

int main()
{
  duration<long, ratio<60>> m(1);
  duration<long, ratio<1>> s(30);
  __CPROVER_assert(to_sec(m).count() == 60, "single conversion");
  __CPROVER_assert(add_secs(m, s).count() == 90, "mixed-period add");
  return 0;
}
