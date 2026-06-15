typedef short __gcc_v8hi __attribute__((__vector_size__(16)));
__gcc_v8hi __builtin_ia32_psrlwi128(__gcc_v8hi, int);

int main()
{
  // Logical (zero-fill) right shift: 0xFFFF (-1) >> 4 == 0x0FFF == 4095,
  // distinguishing it from an arithmetic shift (which would give -1).
  __gcc_v8hi a = (__gcc_v8hi){-1, 16, 3, 4, 5, 6, 7, 8};
  __gcc_v8hi r = __builtin_ia32_psrlwi128(a, 4);
  __CPROVER_assert(r[0] == 4095 && r[1] == 1, "srli epi16");
  return 0;
}
