extern "C" void __CPROVER_assert(bool, const char *);
template <class>
struct W;
template <class T>
struct F
{
  static const int value = 0;
};
// [temp.spec.partial.match]/1, [class.static.data]/4: F<W<T>> matches the
// partial specialization, whose constant member is initialized from F<T>
template <class T>
struct F<W<T>>
{
  static const int value = F<T>::value + 1;
};
int main()
{
  // F<W<W<int>>> must not be instantiated first: then this works
  __CPROVER_assert(F<W<W<W<int>>>>::value == 3, "three levels");
  __CPROVER_assert(F<W<W<int>>>::value == 2, "two levels");
  __CPROVER_assert(F<W<W<W<int>>>>::value != 3, "WRONG (must FAIL)");
}
