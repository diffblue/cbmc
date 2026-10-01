extern "C" void __CPROVER_assert(bool, const char *);
template <class>
struct W;
template <class T>
struct F
{
  static const int value = 0;
};
template <class T>
struct F<W<T>>
{
  static const int value = F<T>::value + 1;
};
// [temp.inst]/16: only the total depth of recursive instantiations is
// bounded (Annex B recommends at least 1024)
int main()
{
  __CPROVER_assert(
    F<W<W<W<W<W<W<W<W<W<W<W<W<int>>>>>>>>>>>>>::value == 12, "twelve levels");
  __CPROVER_assert(
    F<W<W<W<W<W<W<W<W<W<W<W<W<int>>>>>>>>>>>>>::value != 12,
    "WRONG (must FAIL)");
}
