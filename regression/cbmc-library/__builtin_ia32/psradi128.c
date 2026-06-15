typedef int __gcc_v4si __attribute__((__vector_size__(16)));
__gcc_v4si __builtin_ia32_psradi128(__gcc_v4si, int);

int main()
{
  __gcc_v4si a = (__gcc_v4si){-16, 8, -1, 4};
  __gcc_v4si r = __builtin_ia32_psradi128(a, 2); // arithmetic right by 2
  // count >= 32 -> sign fill: -16 -> -1, 8 -> 0
  __gcc_v4si s = __builtin_ia32_psradi128(a, 40);
  __CPROVER_assert(
    r[0] == -4 && r[1] == 2 && s[0] == -1 && s[1] == 0, "srai epi32");
  return 0;
}
