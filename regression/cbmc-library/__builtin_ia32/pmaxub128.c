typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
__gcc_v16qi __builtin_ia32_pmaxub128(__gcc_v16qi, __gcc_v16qi);

int main()
{
  // Lane 0 distinguishes unsigned from signed: -1 is 0xFF, the largest value
  // under unsigned comparison, so the unsigned max of {-1, 0} is -1.
  __gcc_v16qi a =
    (__gcc_v16qi){-1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16};
  __gcc_v16qi b =
    (__gcc_v16qi){0, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
  __gcc_v16qi r = __builtin_ia32_pmaxub128(a, b);
  __CPROVER_assert(r[0] == -1 && r[15] == 16, "max epu8");
  return 0;
}
