extern "C" void __CPROVER_assert(bool, const char *);
template <class>
struct W;
template <class T>
struct F
{
  enum
  {
    value = 0
  };
};
// as main.cpp, with the value an enumerator ([dcl.enum]/2)
template <class T>
struct F<W<T>>
{
  enum
  {
    value = F<T>::value + 1
  };
};
int main()
{
  __CPROVER_assert(F<W<W<W<int>>>>::value == 3, "three levels");
  __CPROVER_assert(F<W<W<W<int>>>>::value != 3, "WRONG (must FAIL)");
}
