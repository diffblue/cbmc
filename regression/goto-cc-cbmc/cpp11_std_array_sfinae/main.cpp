// Minimal `goto-cc` reproducer for the same bug documented in
// regression/cbmc-cpp/cpp11_std_is_swappable_sfinae — that
// processing libstdc++'s `std::array<T, N>` (which transitively
// instantiates `std::__is_swappable_impl<T>` and hits the SFINAE
// substitution in `swap(_Tp&, _Tp&)`'s `_Require<__not_<...>, ...>`
// return type) emits spurious type-checker errors that are
// supposed to be absorbed silently per [temp.deduct]/8.
//
// This version reproduces via `#include <array>` with `goto-cc`
// specifically, because that was the user-facing symptom:
//   goto-cc harness.cpp
// where `harness.cpp` contained `std::array<double, N>` data
// members — the reported problem being "goto-cc doesn't work and
// yields debug output".  "Debug output" here is `irep::pretty()`
// dump leaking into an error message (struct_tag dump with
// `* #source_location:` / `* identifier:` indented sub-fields).

#include <array>

int main()
{
  std::array<double, 3> a{};
  (void)a;
  return 0;
}
