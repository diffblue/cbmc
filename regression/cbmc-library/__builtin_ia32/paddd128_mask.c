typedef int __gcc_v4si __attribute__((__vector_size__(16)));
__gcc_v4si
__builtin_ia32_paddd128_mask(__gcc_v4si, __gcc_v4si, __gcc_v4si, unsigned char);

int main()
{
  __gcc_v4si a = {1, 1, 1, 1};
  __gcc_v4si b = {2, 2, 2, 2};
  __gcc_v4si src = {9, 9, 9, 9};
  // Mask 0x5: bits 0 and 2 set -> a+b (3); lanes 1 and 3 keep the source (9).
  __gcc_v4si r = __builtin_ia32_paddd128_mask(a, b, src, 0x5);
  __CPROVER_assert(
    r[0] == 3 && r[1] == 9 && r[2] == 3 && r[3] == 9, "paddd128 merge-masked");
  return 0;
}
