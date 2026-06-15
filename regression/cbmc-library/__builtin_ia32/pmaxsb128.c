typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
__gcc_v16qi __builtin_ia32_pmaxsb128(__gcc_v16qi, __gcc_v16qi);

int main()
{
  __gcc_v16qi a = (__gcc_v16qi){
    1, -2, 3, -4, 5, -6, 7, -8, 9, -10, 11, -12, 13, -14, 15, -16};
  __gcc_v16qi b = (__gcc_v16qi){
    -1, 2, -3, 4, -5, 6, -7, 8, -9, 10, -11, 12, -13, 14, -15, 16};
  __gcc_v16qi r = __builtin_ia32_pmaxsb128(a, b);
  __CPROVER_assert(r[0] == 1 && r[1] == 2, "max epi8");
  return 0;
}
