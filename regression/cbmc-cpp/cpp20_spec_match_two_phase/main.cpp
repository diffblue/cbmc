// N5008 [temp.res.general]/1 + [temp.dep.candidate]/1 (two-phase name
// lookup): in the partial specialization's non-deduced pattern
// argument `decltype(to_address(_Pointer()))`, the unqualified
// dependent call `to_address(...)` is looked up in the DEFINITION
// context (plus instantiation-point ADL only); `to_address` is
// declared LATER and `int` contributes no ADL namespaces, so
// substitution fails and the PRIMARY must be selected
// ([temp.spec.partial.match]/2, [temp.deduct]/8).  CBMC resolves the
// name at instantiation time regardless of declaration order, wrongly
// selects the specialization, and the trait evaluates TRUE.
// Distilled by cvise from the __and_helper/_IsFancyPointer cascade of
// std::__to_address(reverse_iterator) -- NOTE the reduction drifted
// from the vector-family root to this adjacent genuine defect; the
// harvest is archived in .kiro/reductions/da1_and_helper_23line.cpp.
extern "C" void __CPROVER_assert(bool, const char *);
template <class, class = void> struct HasToAddress
{
  static const bool value = false;
};
// partial spec whose second arg needs a name declared only LATER;
// matching must fail SOFTLY and select the primary
template <class _Pointer>
struct HasToAddress<_Pointer, decltype(to_address(_Pointer()))>
{
  static const bool value = true;
};
template <class _Pointer> void __to_address(_Pointer);
template <class _Pointer>
auto to_address(_Pointer __p) -> decltype(__to_address(__p));

int main()
{
  __CPROVER_assert(
    !HasToAddress<int>::value, "primary selected (soft mismatch)");
  return 0;
}
