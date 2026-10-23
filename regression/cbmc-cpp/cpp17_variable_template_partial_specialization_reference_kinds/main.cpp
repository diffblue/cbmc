extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [temp.spec.partial.match]/2: <int &&, int &> does not match <T, T>
template <class, class>
constexpr bool same_v = false;
template <class T>
constexpr bool same_v<T, T> = true;
template <class A, class B>
struct same
{
  static constexpr bool value = same_v<A, B>;
};
static_assert(!same_v<int &&, int &>, "rvalue vs lvalue reference");
static_assert(!same<int &&, int &>::value, "through a class");
static_assert(same_v<int &&, int &&>, "same");
int main()
{
  __CPROVER_assert(!same_v<int &, int &&>, "lvalue vs rvalue reference");
  __CPROVER_assert(same_v<int &, int &&>, "WRONG (must FAIL)");
  return 0;
}
