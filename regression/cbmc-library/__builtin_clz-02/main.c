#ifdef _MSC_VER
#  define __builtin_clz(x) __lzcnt(x)
#  define _Static_assert static_assert
#endif

int main()
{
  _Static_assert(
    __builtin_clz(0xffU) == 8 * sizeof(unsigned) - 8, "compile-time constant");

  return 0;
}
