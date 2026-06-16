typedef short __gcc_v8hi __attribute__((__vector_size__(16)));
__gcc_v8hi __builtin_ia32_pminsw128(__gcc_v8hi, __gcc_v8hi);

int main()
{
  __gcc_v8hi a = (__gcc_v8hi){1, -2, 3, -4, 5, -6, 7, -8};
  __gcc_v8hi b = (__gcc_v8hi){-1, 2, -3, 4, -5, 6, -7, 8};
  __gcc_v8hi r = __builtin_ia32_pminsw128(a, b);
  __CPROVER_assert(r[0] == -1 && r[1] == -2, "min epi16");
  return 0;
}
