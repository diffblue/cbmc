// N5008 [temp.deduct]/8 + [temp.variadic]/5: distilled from
// cpp20_vector_basic_libcxx's push_back growth path -- the LAST layer
// keeping std::vector wrong under --cpp20 --stdlib libc++.
// std::__to_address(reverse_iterator) must select the operator->
// helper: its dispatch runs libc++'s _And<is_class<RI>,
// _IsFancyPointer<RI>> = decltype(__and_helper<...>(0)) where the
// constrained overload's parameter type expands the pack
// `__expand_to_true<__enable_if_t<_Pred::value>...>`.  The resolve
// cascade (probe evidence): `value` -> `__enable_if_t` ->
// `__expand_to_true` fails, then `type` -> `__enable_if_t` ->
// `__to_address`'s own `!is_pointer` constraint fails, both
// __to_address overloads are discarded, and the enclosing body is
// dropped (in the vector test: __uninitialized_allocator_move_if_
// noexcept returns garbage, INVALID __begin_).
extern "C" void __CPROVER_assert(bool, const char *);
#include <iterator>
#include <memory>
int main()
{
  int arr[2] = {41, 42};
  std::reverse_iterator<int *> rit(arr + 1); // points at arr[0]
  int *raw = std::__to_address(rit);
  __CPROVER_assert(*raw == 41, "to_address of reverse_iterator");
  return 0;
}
