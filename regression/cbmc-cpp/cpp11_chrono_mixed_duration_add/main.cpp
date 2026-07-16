// N5008 [time.duration.nonmember]: operator+ on durations of different
// periods converts both operands to their common_type
// (`__cd(__lhs).count() + __cd(__rhs).count()`) -- minutes(1) + seconds(30)
// is seconds(90).
//
// KNOWNBUG: the body of the instantiated
// std::chrono::operator+(duration<long, ratio<1,1>>, duration<long, ratio<60,1>>)
// fails to convert -- resolution of the local alias `__cd` / the
// `duration` converting-constructor calls inside it finds no match
// (probed: RESOLVE-FAIL 'duration' x3, '__cd') -- and the failure is
// swallowed by the system-header leniency, so the call returns NONDET and
// the sum is garbage.  The pieces work in isolation: same-type operator+,
// duration_cast<seconds>(minutes(1)), and the converting constructor
// `seconds s = m;` all verify; common_type<minutes, seconds> deduces
// seconds correctly.  Only the mixed-period operator+ body is affected.
//
// g++/clang++ verify at runtime.  Flip to CORE when the operator+ body
// converts.
extern "C" void __CPROVER_assert(bool, const char *);
#include <chrono>

int main()
{
  using namespace std::chrono;
  auto d = minutes(1) + seconds(30);
  __CPROVER_assert(duration_cast<seconds>(d).count() == 90, "90 seconds");
  auto e = seconds(30) + minutes(1);
  __CPROVER_assert(e.count() == 90, "commuted");
  return 0;
}
