typedef int __gcc_v16si __attribute__((__vector_size__(64)));
__gcc_v16si __builtin_ia32_paddd512_mask(
  __gcc_v16si,
  __gcc_v16si,
  __gcc_v16si,
  unsigned short);

int main()
{
  __gcc_v16si a = {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1};
  __gcc_v16si b = {2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2};
  __gcc_v16si src = {9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9};
  // Mask 0x0005: bits 0 and 2 set -> those lanes get a+b (3), the rest keep
  // the merge source (9).
  __gcc_v16si r = __builtin_ia32_paddd512_mask(a, b, src, 0x0005);
  __CPROVER_assert(
    r[0] == 3 && r[1] == 9 && r[2] == 3 && r[3] == 9 && r[15] == 9,
    "paddd512 merge-masked add");
  return 0;
}
