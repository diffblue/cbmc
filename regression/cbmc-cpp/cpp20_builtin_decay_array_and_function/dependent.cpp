extern "C" void __CPROVER_assert(bool, const char *);
// [meta.trans.other] decay through an alias template and a member typedef of
// a class template (libstdc++ 16's std::decay is `using type = __decay(_Tp);')
template <typename T, typename U>
constexpr bool same = __is_same(T, U);
template <class T>
using decay_t = __decay(T);
template <class T>
struct D
{
  using type = __decay(T);
};
int main()
{
  __CPROVER_assert(
    same<decay_t<const int(&)[3]>, const int *> &&
      same<typename D<char (&)(int)>::type, char (*)(int)> &&
      same<decay_t<const long &>, long>,
    "dependent");
  __CPROVER_assert(!same<decay_t<int[2]>, int *>, "WRONG (must FAIL)");
}
