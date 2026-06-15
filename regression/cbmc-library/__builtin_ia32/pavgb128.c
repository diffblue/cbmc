typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
__gcc_v16qi __builtin_ia32_pavgb128(__gcc_v16qi, __gcc_v16qi);

int main()
{
  // Lane 0 distinguishes unsigned from signed: -1 is 255 unsigned, so the
  // rounded unsigned average of {255, 1} is (255 + 1 + 1) >> 1 == 128, which
  // is -128 as a signed byte (a signed average would give 0).
  __gcc_v16qi a =
    (__gcc_v16qi){-1, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32};
  __gcc_v16qi b = (__gcc_v16qi){1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4};
  __gcc_v16qi r = __builtin_ia32_pavgb128(a, b);
  __CPROVER_assert(r[0] == -128 && r[1] == 4, "avg epu8");
  return 0;
}
