int main()
{
  long long i;
#ifndef _MSC_VER
  _Static_assert(sizeof(int) == sizeof(*(1 ? ((void *)(0ll)) : (int *)1)), "");
  // We are able to simplify all of the expressions involving i below to 0, but
  // GCC and Clang don't do so. Hence, the static asserts pass for those
  // compilers.
  _Static_assert(
    sizeof(int) != sizeof(*(1 ? ((void *)(i * 0)) : (int *)1)), "");
  _Static_assert(
    sizeof(int) != sizeof(*(1 ? ((void *)(i - i)) : (int *)1)), "");
  _Static_assert(
    sizeof(int) != sizeof(*(1 ? ((void *)(i ? 0ll : 0ll)) : (int *)1)), "");
  _Static_assert(
    sizeof(int) != sizeof(*(1 ? ((void *)(0 ? i : 0ll)) : (int *)1)), "");
#else
  static_assert(sizeof(int) == sizeof(*(1 ? ((void *)(0)) : (int *)1)), "");
  // Visual Studio rejects this as "illegal indirection"
  // static_assert(
  //   sizeof(int) == sizeof(*(1 ? ((void *)(i * 0)) : (int *)1)), "");
#endif
}
