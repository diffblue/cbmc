typedef int __gcc_v4si __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));
__gcc_v4si __builtin_ia32_psubd128(__gcc_v4si, __gcc_v4si);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native -) for all inputs.
  __gcc_v4si a, b;
  __gcc_v4si r = __builtin_ia32_psubd128(a, b);
  __gcc_v4si_u ref = (__gcc_v4si_u)a - (__gcc_v4si_u)b;
  __CPROVER_assert(
    r[0] == (int)ref[0] && r[1] == (int)ref[1] && r[2] == (int)ref[2] &&
      r[3] == (int)ref[3],
    "__builtin_ia32_psubd128 == native -");
  return 0;
}
