extern "C" void __CPROVER_assert(bool, const char *);
// [meta.trans.other] decay of a function type (no reference): a pointer to it
template <typename T, typename U>
constexpr bool same = __is_same(T, U);
int main()
{
  __CPROVER_assert(same<__decay(int(long)), int (*)(long)>, "function type");
  __CPROVER_assert(
    !same<__decay(int(long)), int (*)(long)>, "WRONG (must FAIL)");
}
