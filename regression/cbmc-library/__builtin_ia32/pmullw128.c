typedef short __gcc_v8hi __attribute__((__vector_size__(16)));
__gcc_v8hi __builtin_ia32_pmullw128(__gcc_v8hi, __gcc_v8hi);

int main()
{
  __gcc_v8hi a = (__gcc_v8hi){1, 2, 3, 4, 5, 6, 7, 8};
  __gcc_v8hi b = (__gcc_v8hi){2, 3, 4, 5, 6, 7, 8, 9};
  __gcc_v8hi r = __builtin_ia32_pmullw128(a, b);
  __CPROVER_assert(r[0] == 2 && r[1] == 6 && r[7] == 72, "mullo epi16");
  return 0;
}
