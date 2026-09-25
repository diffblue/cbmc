// libc++ std::variant: the converting constructor selects the alternative
// through `__best_match_t' -- an overload set built from a base pack
// (`struct __all_overloads : _Bases... { using _Bases::operator()...; }',
// N5008 [namespace.udecl]/1 pack expansion) whose members return through a
// narrowing check `__test_impl<_Dest>({std::declval<_Source>()})' with an
// array-reference parameter `_Dest (&&)[1]' ([dcl.init.list]/3.4,
// [dcl.init.ref]/5.4.2), plus the five `__traits' static members computed by
// a constexpr function over an initializer_list.  Each was a separate
// front-end gap (rounds 160-161); the non-vacuous checks below cover the
// resulting object model.
#include <variant>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::variant<int, double> v = 42;
  __CPROVER_assert(v.index() == 0, "index");
  __CPROVER_assert(std::holds_alternative<int>(v), "holds int");
  __CPROVER_assert(std::get<int>(v) == 42, "get<int>");
  __CPROVER_assert(std::get<0>(v) == 42, "get<0>");
  v = 2.5;
  __CPROVER_assert(
    v.index() == 1 && std::get<double>(v) == 2.5, "assign double");
  std::variant<int, double> w(std::in_place_index<1>, 1.5);
  __CPROVER_assert(w.index() == 1, "in_place_index");
  __CPROVER_assert(std::get<1>(w) == 2.5, "WRONG (must FAIL)");
}
