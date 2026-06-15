typedef short __gcc_v8hi __attribute__((__vector_size__(16)));
__gcc_v8hi __builtin_ia32_paddsw128(__gcc_v8hi, __gcc_v8hi);

int main()
{
  // Signed 16-bit saturation: 30000+10000 clamps to 32767; -30000+-10000 to
  // -32768.
  __gcc_v8hi a = (__gcc_v8hi){30000, -30000, 3, 4, 5, 6, 7, 8};
  __gcc_v8hi b = (__gcc_v8hi){10000, -10000, 1, 1, 1, 1, 1, 1};
  __gcc_v8hi r = __builtin_ia32_paddsw128(a, b);
  __CPROVER_assert(r[0] == 32767 && r[1] == -32768 && r[2] == 4, "adds epi16");
  return 0;
}
