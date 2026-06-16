typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
__gcc_v16qi __builtin_ia32_pminsb128(__gcc_v16qi, __gcc_v16qi);

int main()
{
  __gcc_v16qi a = (__gcc_v16qi){
    1, -2, 3, -4, 5, -6, 7, -8, 9, -10, 11, -12, 13, -14, 15, -16};
  __gcc_v16qi b = (__gcc_v16qi){
    -1, 2, -3, 4, -5, 6, -7, 8, -9, 10, -11, 12, -13, 14, -15, 16};
  __gcc_v16qi r = __builtin_ia32_pminsb128(a, b);
  // Compare as bytes: -1, -2 cast to char yield 0xFF, 0xFE on either
  // signedness.
  __CPROVER_assert(r[0] == (char)-1 && r[1] == (char)-2, "min epi8");
  return 0;
}
