int main()
{
#ifdef __GNUC__
  _Static_assert(
    __builtin_clz(0xffU) == 8 * sizeof(unsigned) - 8,
    "GCC/Clang compile-time constant");
#endif

  return 0;
}
