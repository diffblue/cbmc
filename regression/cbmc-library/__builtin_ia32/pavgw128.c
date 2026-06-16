typedef short __gcc_v8hi __attribute__((__vector_size__(16)));
__gcc_v8hi __builtin_ia32_pavgw128(__gcc_v8hi, __gcc_v8hi);

int main()
{
  // Lane 0 distinguishes unsigned from signed: -1 is 65535 unsigned, so the
  // rounded unsigned average of {65535, 1} is (65535 + 1 + 1) >> 1 == 32768,
  // which is -32768 as a signed 16-bit value (a signed average would give 0).
  __gcc_v8hi a = (__gcc_v8hi){-1, 4, 6, 8, 10, 12, 14, 16};
  __gcc_v8hi b = (__gcc_v8hi){1, 4, 4, 4, 4, 4, 4, 4};
  __gcc_v8hi r = __builtin_ia32_pavgw128(a, b);
  __CPROVER_assert(r[0] == -32768 && r[1] == 4, "avg epu16");
  return 0;
}
