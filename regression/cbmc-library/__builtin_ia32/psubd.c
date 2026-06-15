typedef int __gcc_v2si __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));
__gcc_v2si __builtin_ia32_psubd(__gcc_v2si, __gcc_v2si);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native -) for all inputs.
  __gcc_v2si a, b;
  __gcc_v2si r = __builtin_ia32_psubd(a, b);
  __gcc_v2si_u ref = (__gcc_v2si_u)a - (__gcc_v2si_u)b;
  __CPROVER_assert(
    r[0] == (int)ref[0] && r[1] == (int)ref[1],
    "__builtin_ia32_psubd == native -");
  return 0;
}
