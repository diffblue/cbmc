typedef int __gcc_v4si __attribute__((__vector_size__(16)));
__gcc_v4si __builtin_ia32_pmaxud128(__gcc_v4si, __gcc_v4si);

int main()
{
  // Lane 0 distinguishes unsigned from signed: -1 is 0xFFFFFFFF, the largest
  // value under unsigned comparison, so the unsigned max of {-1, 0} is -1
  // (a signed max would pick 0).
  __gcc_v4si a = (__gcc_v4si){-1, 2, 3, 4};
  __gcc_v4si b = (__gcc_v4si){0, 3, 2, 1};
  __gcc_v4si r = __builtin_ia32_pmaxud128(a, b);
  __CPROVER_assert(r[0] == -1 && r[3] == 4, "max epu32");
  return 0;
}
