// libstdc++'s std::__and_ (13: `__and_fn(int) -> __first_t<true_type,
// __enable_if_t<bool(_Bn::value)>...>') -- the pack reference `_Bn' sits
// inside the parser-form function type of the ambiguous `bool(_Bn::value)'
// ([temp.arg]/1: function type or functional cast).  It was substituted for
// the first pack element only, so `__and_<true_type, false_type>' was
// true_type: every libstdc++ trait built on __and_ with a false alternative
// after the first was wrong (std::pair's converting-constructor constraints
// among them).  N5008 [temp.variadic]/5.
#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  __CPROVER_assert(!std::__and_<std::true_type, std::false_type>::value, "t f");
  __CPROVER_assert(!std::__and_<std::false_type, std::true_type>::value, "f t");
  __CPROVER_assert(std::__and_<std::true_type, std::true_type>::value, "t t");
  __CPROVER_assert(
    !std::__and_<std::true_type, std::true_type, std::false_type>::value,
    "t t f");
  __CPROVER_assert(std::__and_<>::value, "empty conjunction");
  __CPROVER_assert(
    std::__or_<std::false_type, std::true_type>::value, "or f t");
  __CPROVER_assert(
    !std::__or_<std::false_type, std::false_type>::value, "or f f");
  return 0;
}
