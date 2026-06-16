typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
__gcc_v16qi __builtin_ia32_psubusb128(__gcc_v16qi, __gcc_v16qi);

int main()
{
  // Unsigned saturating subtract: 10-20 clamps to 0; the bytes 200-100 == 100.
  __gcc_v16qi a =
    (__gcc_v16qi){10, 200, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16};
  __gcc_v16qi b =
    (__gcc_v16qi){20, 100, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1};
  __gcc_v16qi r = __builtin_ia32_psubusb128(a, b);
  __CPROVER_assert(r[0] == 0 && r[1] == 100, "subs epu8");
  return 0;
}
