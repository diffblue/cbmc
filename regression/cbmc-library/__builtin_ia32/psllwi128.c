typedef short __gcc_v8hi __attribute__((__vector_size__(16)));
__gcc_v8hi __builtin_ia32_psllwi128(__gcc_v8hi, int);

int main()
{
  __gcc_v8hi a = (__gcc_v8hi){1, 2, 3, 4, 5, 6, 7, 8};
  __gcc_v8hi r = __builtin_ia32_psllwi128(a, 4);  // logical left by 4
  __gcc_v8hi z = __builtin_ia32_psllwi128(a, 20); // count >= 16 -> 0
  __CPROVER_assert(r[0] == 16 && r[1] == 32 && z[0] == 0, "slli epi16");
  return 0;
}
