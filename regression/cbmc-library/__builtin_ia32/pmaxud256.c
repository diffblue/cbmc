typedef int __gcc_v8si __attribute__((__vector_size__(32)));
__gcc_v8si __builtin_ia32_pmaxud256(__gcc_v8si, __gcc_v8si);

int main()
{
  // Lane 0: -1 is 0xFFFFFFFF, the unsigned max of {-1, 0}.
  __gcc_v8si a = (__gcc_v8si){-1, 2, 3, 4, 5, 6, 7, 8};
  __gcc_v8si b = (__gcc_v8si){0, 3, 2, 1, 0, 0, 0, 0};
  __gcc_v8si r = __builtin_ia32_pmaxud256(a, b);
  __CPROVER_assert(r[0] == -1 && r[3] == 4, "max epu32 (256)");
  return 0;
}
