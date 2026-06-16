typedef int __gcc_v4si __attribute__((__vector_size__(16)));
__gcc_v4si __builtin_ia32_pminsd128(__gcc_v4si, __gcc_v4si);

int main()
{
  __gcc_v4si a = (__gcc_v4si){1, -2, 3, -4};
  __gcc_v4si b = (__gcc_v4si){-1, 2, -3, 4};
  __gcc_v4si r = __builtin_ia32_pminsd128(a, b);
  __CPROVER_assert(r[0] == -1 && r[1] == -2, "min epi32");
  return 0;
}
