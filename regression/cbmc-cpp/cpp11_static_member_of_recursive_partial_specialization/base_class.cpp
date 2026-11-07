extern "C" void __CPROVER_assert(bool, const char *);
template <int v>
struct constant
{
  static const int value = v;
};
template <class>
struct W;
template <class T>
struct F : constant<0>
{
};
// as main.cpp, with the value inherited from a base class: libc++'s
// __find_max_align<__type_list<_Hp, _Tp>, _Len>, used by the default
// argument of std::aligned_storage
template <class T>
struct F<W<T>> : constant<F<T>::value + 1>
{
};
int main()
{
  __CPROVER_assert(F<W<W<W<int>>>>::value == 3, "three levels");
  __CPROVER_assert(F<W<W<W<int>>>>::value != 3, "WRONG (must FAIL)");
}
