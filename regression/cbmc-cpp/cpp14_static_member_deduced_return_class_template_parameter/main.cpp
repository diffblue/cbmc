extern "C" void __CPROVER_assert(bool, const char *);
template <typename T, typename U>
inline constexpr bool is_same_v = false;
template <typename T>
inline constexpr bool is_same_v<T, T> = true;
template <typename>
struct gen;
template <typename R>
struct gen<R (*)()>
{
  // N5008 [temp.inst]/4, [dcl.spec.auto.general]/15: the member is
  // instantiated with the class's template argument R = int when the call
  // below needs its deduced return type
  static auto invoke()
  {
    return is_same_v<R, int>;
  }
};
int main()
{
  bool r = gen<int (*)()>::invoke();
  __CPROVER_assert(r, "deduced from R");
  __CPROVER_assert(!r, "WRONG (must FAIL)");
  return 0;
}
