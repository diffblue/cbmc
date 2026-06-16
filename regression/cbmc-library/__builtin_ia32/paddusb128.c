typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
__gcc_v16qi __builtin_ia32_paddusb128(__gcc_v16qi, __gcc_v16qi);

int main()
{
  // Unsigned saturation: the bytes 200 and 100 (written as their signed-char
  // equivalents) sum to 300, which clamps to 255 == -1 as a signed byte.
  __gcc_v16qi a =
    (__gcc_v16qi){200, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16};
  __gcc_v16qi b =
    (__gcc_v16qi){100, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1};
  __gcc_v16qi r = __builtin_ia32_paddusb128(a, b);
  __CPROVER_assert(r[0] == -1 && r[1] == 2, "adds epu8");
  return 0;
}
