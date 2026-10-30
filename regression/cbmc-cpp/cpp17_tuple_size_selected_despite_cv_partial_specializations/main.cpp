extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;
template <class T, size_t v>
struct integral_constant
{
  static const size_t value = v;
};
template <class...>
class tuple;
template <class T>
struct tuple_size;
// libc++'s <__tuple/tuple_size.h>: the cv-qualified partial
// specializations are guarded by an alias whose second argument is only
// well-formed when tuple_size<T> is complete ([temp.deduct.general]/8)
template <class T, class...>
using enable_if_tuple_size_imp = T;
template <class T>
struct tuple_size<enable_if_tuple_size_imp<
  const volatile T,
  integral_constant<size_t, sizeof(tuple_size<T>)>>>;
template <class T>
struct tuple_size<enable_if_tuple_size_imp<
  const T,
  integral_constant<size_t, sizeof(tuple_size<T>)>>>
  : integral_constant<size_t, tuple_size<T>::value>
{
};
template <class... T>
struct tuple_size<tuple<T...>> : integral_constant<size_t, sizeof...(T)>
{
};
static_assert(tuple_size<tuple<int, int>>::value == 2, "tuple_size");
static_assert(tuple_size<const tuple<int, char, int>>::value == 3, "const");
int main()
{
  tuple_size<tuple<int, int>> t;
  // [temp.spec.partial.match]/1: tuple_size<tuple<T...>> is selected, so
  // the specialization has its base class
  integral_constant<size_t, 2> *base = &t;
  __CPROVER_assert(base->value == 2, "the base of the selected specialization");
  __CPROVER_assert(tuple_size<tuple<int, int>>::value == 2, "value");
  __CPROVER_assert(tuple_size<const tuple<int>>::value == 1, "const tuple");
  __CPROVER_assert(
    tuple_size<tuple<int, int>>::value == 3, "WRONG (must FAIL)");
}
