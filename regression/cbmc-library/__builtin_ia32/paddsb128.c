typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
__gcc_v16qi __builtin_ia32_paddsb128(__gcc_v16qi, __gcc_v16qi);

int main()
{
  // Signed saturation: 100+50=150 clamps to 127; -100+-50=-150 clamps to -128.
  __gcc_v16qi a =
    (__gcc_v16qi){100, -100, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16};
  __gcc_v16qi b =
    (__gcc_v16qi){50, -50, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1};
  __gcc_v16qi r = __builtin_ia32_paddsb128(a, b);
  __CPROVER_assert(r[0] == 127 && r[1] == -128 && r[2] == 4, "adds epi8");
  return 0;
}
