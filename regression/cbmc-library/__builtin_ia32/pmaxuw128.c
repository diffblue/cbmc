typedef short __gcc_v8hi __attribute__((__vector_size__(16)));
__gcc_v8hi __builtin_ia32_pmaxuw128(__gcc_v8hi, __gcc_v8hi);

int main()
{
  // Lane 0 distinguishes unsigned from signed: -1 is 0xFFFF, the largest
  // value under unsigned comparison, so the unsigned max of {-1, 0} is -1.
  __gcc_v8hi a = (__gcc_v8hi){-1, 2, 3, 4, 5, 6, 7, 8};
  __gcc_v8hi b = (__gcc_v8hi){0, 7, 6, 5, 4, 3, 2, 1};
  __gcc_v8hi r = __builtin_ia32_pmaxuw128(a, b);
  __CPROVER_assert(r[0] == -1 && r[7] == 8, "max epu16");
  return 0;
}
